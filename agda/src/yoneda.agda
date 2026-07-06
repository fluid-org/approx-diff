{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_; Level; lift; lower)
open import Data.Product using (_,_; Σ-syntax) renaming (_×_ to _×S_)
open import prop using (lift; lower; _,_; LiftS; liftS)
open import prop-setoid
  using (Setoid; IsEquivalence; module ≈-Reasoning; _∘S_; idS)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; mk-≃m to mk-≈s; ⊗-setoid to _×s_)
open import categories using (Category; HasProducts; IsProduct; HasExponentials; HasTerminal)
open import functor using ([_⇒_]; Functor; NatTrans; ≃-NatTrans;
  HasLimits';
  preserve-limits-of-shape; IsLimit; constF; constF-F; constFmor;
  _∘F_; id; _∘H_; _∘_; ≃-isEquivalence; Id)
open import monad using (Monad)
open import setoid-cat using (SetoidCat; Setoid-terminal; Setoid-products; Setoid-Limit'; Setoid-coproducts)

-- extra 'os' level is to raise the level of the codomain if needed
module yoneda {o m e} os (𝒞 : Category o m e) where

private
  ℓ : Level
  ℓ = o ⊔ m ⊔ e ⊔ os

  module 𝒞 = Category 𝒞

PSh : Category (suc ℓ) ℓ ℓ
PSh = [ 𝒞.opposite ⇒ SetoidCat ℓ ℓ ]

open Setoid
open _⇒s_
open _≈s_
open IsEquivalence
open Functor
open NatTrans
open ≃-NatTrans

atObj : 𝒞.obj → Functor PSh (SetoidCat ℓ ℓ)
atObj x .fobj F = F .fobj x
atObj x .fmor α = α .transf x
atObj x .fmor-cong α₁≈α₂ = α₁≈α₂ .transf-eq x
atObj x .fmor-id .func-eq eq = eq
atObj x .fmor-comp f g .func-eq eq = f .transf x .func-resp-≈ (g .transf x .func-resp-≈ eq)

よ₀ : 𝒞.obj → PSh .Category.obj
よ₀ x .fobj y = Category.hom-setoid-l 𝒞 ℓ ℓ y x
よ₀ x .fmor f .func (lift g) = lift (g 𝒞.∘ f)
よ₀ x .fmor f .func-resp-≈ (lift g₁≈g₂) = lift (𝒞.∘-cong g₁≈g₂ 𝒞.≈-refl)
よ₀ x .fmor-cong {y} {z} {f₁} {f₂} f₁≈f₂ .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.∘-cong g₁≈g₂ f₁≈f₂)
よ₀ x .fmor-id {y} .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.isEquiv .trans 𝒞.id-right g₁≈g₂)
よ₀ x .fmor-comp {y} {z} {w} f g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  begin
    h₁ 𝒞.∘ (g 𝒞.∘ f)  ≈⟨ 𝒞.∘-cong h₁≈h₂ 𝒞.≈-refl ⟩
    h₂ 𝒞.∘ (g 𝒞.∘ f)  ≈˘⟨ 𝒞.assoc _ _ _ ⟩
    (h₂ 𝒞.∘ g) 𝒞.∘ f  ∎
  where open ≈-Reasoning 𝒞.isEquiv

よ : Functor 𝒞 PSh
よ .fobj = よ₀
よ .fmor f .transf y .func (lift g) = lift (f 𝒞.∘ g)
よ .fmor f .transf y .func-resp-≈ (lift g₁≈g₂) = lift (𝒞.∘-cong 𝒞.≈-refl g₁≈g₂)
よ .fmor f .natural g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  begin ((f 𝒞.∘ h₁) 𝒞.∘ g)   ≈⟨ 𝒞.∘-cong (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) 𝒞.≈-refl ⟩
         ((f 𝒞.∘ h₂) 𝒞.∘ g)  ≈⟨ 𝒞.assoc _ _ _ ⟩
         (f 𝒞.∘ (h₂ 𝒞.∘ g))  ∎
  where open ≈-Reasoning 𝒞.isEquiv
よ .fmor-cong {x} {y} {f₁} {f₂} f₁≈f₂ .transf-eq z .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.∘-cong f₁≈f₂ g₁≈g₂)
よ .fmor-id .transf-eq x .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) .lower = 𝒞.isEquiv .trans 𝒞.id-left g₁≈g₂
よ .fmor-comp f g .transf-eq x .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  𝒞.isEquiv .trans (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) (𝒞.assoc _ _ _)

------------------------------------------------------------------------------
-- Yoneda lemma

lemma : ∀ F x → F .fobj x ⇒s Category.hom-setoid PSh (よ₀ x) F
lemma F x .func Fx .transf y .func (lift f) = F .fmor f .func Fx
lemma F x .func Fx .transf y .func-resp-≈ {lift f₁} {lift f₂} (lift f₁≈f₂) =
  F .fmor-cong f₁≈f₂ .func-eq (F .fobj x .refl)
lemma F x .func Fx .natural {y} {z} g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) =
  begin
    F .fmor g .func (F .fmor h₁ .func Fx)
  ≈⟨ F .fmor g .func-resp-≈ (F .fmor-cong h₁≈h₂ .func-eq (F .fobj x .refl)) ⟩
    F .fmor g .func (F .fmor h₂ .func Fx)
  ≈˘⟨ F .fmor-comp _ _ .func-eq (F .fobj x .refl) ⟩
    F .fmor (h₂ 𝒞.∘ g) .func Fx
  ∎ where open ≈-Reasoning (F .fobj z .isEquivalence)
lemma F x .func-resp-≈ {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq y .func-eq {lift f₁} {lift f₂} (lift f₁≈f₂) =
  F .fmor-cong f₁≈f₂ .func-eq Fx₁≈Fx₂

lemma⁻¹ : ∀ F x → Category.hom-setoid PSh (よ₀ x) F ⇒s F .fobj x
lemma⁻¹ F x .func α = α .transf x .func (lift (𝒞.id _))
lemma⁻¹ F x .func-resp-≈ {α₁}{α₂} α₁≈α₂ = α₁≈α₂ .transf-eq x .func-eq (lift 𝒞.≈-refl)

よ⁻¹ : ∀ {x y} → NatTrans (よ₀ x) (よ₀ y) → x 𝒞.⇒ y
よ⁻¹ {x} {y} α = lemma⁻¹ (よ₀ y) x .func α .lower

lemma∘lemma⁻¹ : ∀ F x → (lemma F x ∘S lemma⁻¹ F x) ≈s idS (Category.hom-setoid PSh (よ₀ x) F)
lemma∘lemma⁻¹ F x .func-eq {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq y .func-eq {lift f} {lift g} (lift f≈g) =
  F .fobj y .trans
      (Fx₁ .natural f .func-eq (lift 𝒞.≈-refl))
      (Fx₁≈Fx₂ .transf-eq y .func-eq (lift (𝒞.≈-trans 𝒞.id-left f≈g)))

lemma⁻¹∘lemma : ∀ F x → (lemma⁻¹ F x ∘S lemma F x) ≈s idS (F .fobj x)
lemma⁻¹∘lemma F x .func-eq {Fx₁} {Fx₂} Fx₁≈Fx₂ = F .fmor-id .func-eq Fx₁≈Fx₂

-- lemma-natural-x : ∀ {F x y} (f : x 𝒞.⇒ y) →
--                 (lemma F x ∘S F .fmor f) ≈s ({!!} ∘S lemma F y)
-- lemma-natural-x f = {!!}

------------------------------------------------------------------------------
-- Completeness

import functor-cat-limits

limits : (𝒮 : Category o m e) → HasLimits' 𝒮 PSh
limits 𝒮 = functor-cat-limits.limits _ _ _ (Setoid-Limit' ℓ 𝒮)

-- products as a special case, using a nicer intensional representation.
open import functor-cat-products
       𝒞.opposite
       (SetoidCat ℓ ℓ)
       (Setoid-terminal _ _)
       (Setoid-products _ _)
  public

------------------------------------------------------------------------------
-- FIXME: cocompleteness

open import functor-cat-coproducts
       𝒞.opposite
       (SetoidCat ℓ ℓ)
       (Setoid-coproducts _ _)
  public

------------------------------------------------------------------------------
-- Exponentials
module _ where

  open HasProducts products

  _⟶_ : PSh .Category.obj → PSh .Category.obj → PSh .Category.obj
  (F ⟶ G) .fobj x = Category.hom-setoid PSh (F × (よ .fobj x)) G
  (F ⟶ G) .fmor f .func x .transf y .func (a , lift b) = x .transf y .func (a , (lift (f 𝒞.∘ b)))
  (F ⟶ G) .fmor f .func x .transf y .func-resp-≈ (x₁≈x₂ , lift e) =
    x .transf y .func-resp-≈ (x₁≈x₂ , (lift (𝒞.∘-cong (𝒞.≈-refl) e)))
  (F ⟶ G) .fmor f .func h .natural {y}{z} g .func-eq (a₁≈a₂ , lift e) =
    G .fobj z .trans
      (h .natural g .func-eq (a₁≈a₂ , lift (𝒞.∘-cong 𝒞.≈-refl e)))
      (h .transf z .func-resp-≈ (F .fobj z .Setoid.refl , lift (𝒞.assoc _ _ _)))
  (F ⟶ G) .fmor f .func-resp-≈ {h₁}{h₂} h₁≈h₂ .transf-eq x .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq x .func-eq (a₁≈a₂ , (lift (𝒞.∘-cong 𝒞.≈-refl e)))
  (F ⟶ G) .fmor-cong f≈g .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift (𝒞.∘-cong f≈g e))
  (F ⟶ G) .fmor-id .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift (𝒞.≈-trans 𝒞.id-left e))
  (F ⟶ G) .fmor-comp f g .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq
      (a₁≈a₂ ,
       lift (𝒞.≈-trans (𝒞.assoc _ _ _)
                        (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong 𝒞.≈-refl e))))

  eval : ∀ {F G} → NatTrans ((F ⟶ G) × F) G
  eval .transf x .func (g , a) = g .transf x .func (a , lift (𝒞.id x))
  eval .transf x .func-resp-≈ (e , a₁≈a₂) = e .transf-eq x .func-eq (a₁≈a₂ , lift 𝒞.≈-refl)
  eval {F} {G} .natural {x} {y} f .func-eq {h₁ , a₁} {h₂ , a₂} (h₁≈h₂ , a₁≈a₂) =
    G .fobj y .trans
      (h₁ .natural f .func-eq (a₁≈a₂ , lift 𝒞.≈-refl))
      (h₁≈h₂ .transf-eq y .func-eq (F .fobj y .refl , lift 𝒞.id-swap))

  lambda⟶ : ∀ {F G H} → NatTrans (F × G) H → NatTrans F (G ⟶ H)
  lambda⟶ {F} f .transf x .func Fx .transf y .func (Gy , lift g) =
    f .transf y .func (F .fmor g .func Fx , Gy)
  lambda⟶ {F} f .transf x .func Fx .transf y .func-resp-≈ {Gy₁ , lift g₁} {Gy₂ , lift g₂} (Gy₁≈Gy₂ , lift g₁≈g₂) =
    f .transf y .func-resp-≈ (F .fmor-cong g₁≈g₂ .func-eq (F .fobj x .refl) , Gy₁≈Gy₂)
  lambda⟶ {F}{G}{H} f .transf x .func Fx .natural {y} {z} g .func-eq {Gy₁ , lift h₁} {Gy₂ , lift h₂} (Gy₁≈Gy₂ , lift h₁≈h₂) =
    H .fobj z .trans
      (f .natural g .func-eq (F .fmor-cong h₁≈h₂ .func-eq (F .fobj x .refl) , Gy₁≈Gy₂))
      (f .transf z .func-resp-≈ ((F .fobj z .sym (F .fmor-comp _ _ .func-eq (F .fobj x .refl))) , G .fobj z .refl))
  lambda⟶ {F} f .transf x .func-resp-≈ {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq y .func-eq {Gy₁ , lift h₁} {Gy₂ , lift h₂} (Gy₁≈Gy₂ , lift h₁≈h₂) =
    f .transf y .func-resp-≈ (F .fmor-cong h₁≈h₂ .func-eq Fx₁≈Fx₂ , Gy₁≈Gy₂)
  lambda⟶ {F} f .natural {x} {y} g .func-eq {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq z .func-eq {Gz₁ , lift h₁} {Gz₂ , lift h₂} (Gz₁≈Gz₂ , lift h₁≈h₂) =
    f .transf z .func-resp-≈
      (F .fobj z .trans (F .fmor-comp h₁ g .func-eq Fx₁≈Fx₂)
                        (F .fmor-cong h₁≈h₂ .func-eq (F .fobj y .refl)) ,
       Gz₁≈Gz₂)

  exponentials : HasExponentials PSh products
  exponentials .HasExponentials.exp = _⟶_
  exponentials .HasExponentials.eval = eval
  exponentials .HasExponentials.lambda = lambda⟶
  exponentials .HasExponentials.lambda-cong {F} {G} {H} f₁≈f₂ .transf-eq x .func-eq Fx₁≈Fx₂ .transf-eq y .func-eq (Gy₁≈Gy₂ , lift h₁≈h₂) =
    f₁≈f₂ .transf-eq y .func-eq (F .fmor-cong h₁≈h₂ .func-eq Fx₁≈Fx₂ , Gy₁≈Gy₂)
  exponentials .HasExponentials.eval-lambda {F} {G} {H} f .transf-eq x .func-eq (Fx₁≈Fx₂ , Gx₁≈Gx₂) =
    f .transf x .func-resp-≈ (F .fmor-id .func-eq Fx₁≈Fx₂ , Gx₁≈Gx₂)
  exponentials .HasExponentials.lambda-ext {F} {G} {H} f .transf-eq x .func-eq Fx₁≈Fx₂ .transf-eq y .func-eq {Gy₁ , lift h₁} {Gy₂ , lift h₂} (Gy₁≈Gy₂ , lift h₁≈h₂) =
    H .fobj y .trans
      (H .fobj y .sym (f .natural h₁ .func-eq (F .fobj x .sym Fx₁≈Fx₂) .transf-eq y .func-eq (G .fobj y .refl , lift 𝒞.≈-refl)))
      (f .transf x .func _ .transf y .func-resp-≈ (Gy₁≈Gy₂ , lift (𝒞.≈-trans 𝒞.id-right h₁≈h₂)))

------------------------------------------------------------------------------
{-
-- よ preserves products. FIXME: extend this to all limits by copying
-- the proofs from cmon-category.

open IsProduct

preserve-products : ∀ (x y p : 𝒞.obj) (p₁ : p 𝒞.⇒ x) (p₂ : p 𝒞.⇒ y) →
                    IsProduct 𝒞 x y p p₁ p₂ →
                    IsProduct PSh (よ₀ x) (よ₀ y) (よ₀ p) (よ .fmor p₁) (よ .fmor p₂)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .transf z .func Zz .lower =
  p-isproduct .pair (f .transf z .func Zz .lower) (g .transf z .func Zz .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .transf z .func-resp-≈ {Zz₁} {Zz₂} Zz₁≈Zz₂ .lower =
  p-isproduct .pair-cong (f .transf z .func-resp-≈ Zz₁≈Zz₂ .lower) (g .transf z .func-resp-≈ Zz₁≈Zz₂ .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .natural {x₁} {y₁} h .func-eq {Zz₁} {Zz₂} e .lower =
  begin
    p-isproduct .pair (f .transf x₁ .func Zz₁ .lower) (g .transf x₁ .func Zz₁ .lower) 𝒞.∘ h
  ≈⟨ pair-natural p-isproduct _ _ _ ⟩
    p-isproduct .pair (f .transf x₁ .func Zz₁ .lower 𝒞.∘ h) (g .transf x₁ .func Zz₁ .lower 𝒞.∘ h)
  ≈⟨ p-isproduct .pair-cong (f .natural h .func-eq e .lower) (g .natural h .func-eq e .lower) ⟩
    p-isproduct .pair (f .transf y₁ .func (Z .fmor h .func Zz₂) .lower) (g .transf y₁ .func (Z .fmor h .func Zz₂) .lower)
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-cong {Z} f₁≈f₂ g₁≈g₂ .transf-eq w .func-eq e .lower =
  p-isproduct .pair-cong (f₁≈f₂ .transf-eq w .func-eq e .lower) (g₁≈g₂ .transf-eq w .func-eq e .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair-p₁ {Z} f g .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p₁ 𝒞.∘ p-isproduct .pair (f .transf w .func Zw₁ .lower) (g .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-p₁ _ _ ⟩
    f .transf w .func Zw₁ .lower
  ≈⟨ f .transf w .func-resp-≈ e .lower ⟩
    f .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-p₂ {Z} f g .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p₂ 𝒞.∘ p-isproduct .pair (f .transf w .func Zw₁ .lower) (g .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-p₂ _ _ ⟩
    g .transf w .func Zw₁ .lower
  ≈⟨ g .transf w .func-resp-≈ e .lower ⟩
    g .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-ext {Z} f .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p-isproduct .pair (p₁ 𝒞.∘ f .transf w .func Zw₁ .lower) (p₂ 𝒞.∘ f .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-ext _ ⟩
    f .transf w .func Zw₁ .lower
  ≈⟨ f .transf w .func-resp-≈ e .lower ⟩
    f .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
-}

------------------------------------------------------------------------------
-- Yoneda embedding preserves all limits
preserve-limits : ∀ {o₁ m₁ e₁} (𝒮 : Category o₁ m₁ e₁) → preserve-limits-of-shape 𝒮 よ
preserve-limits 𝒮 D apex cone isLimit = lim
  where
  open IsLimit

  conv-transf : ∀ {X x} → NatTrans (constF 𝒮 X) (よ ∘F D) → X .fobj x .Carrier → NatTrans (constF 𝒮 x) D
  conv-transf {X} {x} α Xx .transf s = α .transf s .transf x .func Xx .lower
  conv-transf {X} {x} α Xx .natural f = 𝒞.≈-trans (α .natural f .transf-eq x .func-eq (X .fobj x .refl) .lower) (𝒞.≈-sym 𝒞.id-right)

  conv-transf-≈ : ∀ {X x α₁ α₂ Xx₁ Xx₂} →
                    ≃-NatTrans α₁ α₂ →
                    X .fobj x ._≈_ Xx₁ Xx₂ →
                    ≃-NatTrans (conv-transf {X} {x} α₁ Xx₁) (conv-transf {X} {x} α₂ Xx₂)
  conv-transf-≈ {X} {x} α₁≈α₂ Xx₁≈Xx₂ .transf-eq s = α₁≈α₂ .transf-eq s .transf-eq x .func-eq Xx₁≈Xx₂ .lower

  lim : IsLimit (よ ∘F D) (よ .fobj apex) ((id _ ∘H cone) ∘ constF-F よ apex)
  lim .lambda X α .transf x .func Xx .lower =
    isLimit .lambda x (conv-transf α Xx)
  lim .lambda X α .transf x .func-resp-≈ Xx₁≈Xx₂ .lower =
    isLimit .lambda-cong (conv-transf-≈ (≃-isEquivalence .IsEquivalence.refl) Xx₁≈Xx₂)
  lim .lambda X α .natural {x} {y} f .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower =
    begin
      isLimit .lambda x (conv-transf α Xx₁) 𝒞.∘ f
    ≈⟨ lambda-natural isLimit (conv-transf α Xx₁) f ⟩
      isLimit .lambda y (conv-transf α Xx₁ ∘ constFmor f)
    ≈⟨ isLimit .lambda-cong (record { transf-eq = λ s → α .transf s .natural f .func-eq Xx₁≈Xx₂ .lower }) ⟩
      isLimit .lambda y (conv-transf α (X .fmor f .func Xx₂))
    ∎
    where open ≈-Reasoning 𝒞.isEquiv
  lim .lambda-cong α≈β .transf-eq x .func-eq Xx₁≈Xx₂ .lower =
    isLimit .lambda-cong (conv-transf-≈ α≈β Xx₁≈Xx₂)
  lim .lambda-eval {X} α .transf-eq s .transf-eq x .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower =
    𝒞.≈-trans (isLimit .lambda-eval (conv-transf α Xx₁) .transf-eq s)
               (α .transf s .transf x .func-resp-≈ Xx₁≈Xx₂ .lower)
  lim .lambda-ext {X} f .transf-eq x .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower = begin
      isLimit .lambda x (conv-transf (((id よ ∘H cone) ∘ constF-F よ apex) ∘ constFmor f) Xx₁)
    ≈⟨ isLimit .lambda-cong (record { transf-eq = λ s → 𝒞.≈-refl }) ⟩
      isLimit .lambda x (cone ∘ constFmor (f .transf x .func Xx₁ .lower))
    ≈⟨ isLimit .lambda-ext _ ⟩
      f .transf x .func Xx₁ .lower
    ≈⟨ f .transf x .func-resp-≈ Xx₁≈Xx₂ .lower ⟩
      f .transf x .func Xx₂ .lower
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

-- FIXME: Yoneda embedding also preserves exponentials. Slick proof given here:
--
--   https://math.stackexchange.com/questions/3511252/show-that-the-yoneda-embedding-preserves-exponential-objects?rq=1

------------------------------------------------------------------------------
-- A little bit of coends

open import product-category using (product; pairF; project₁; project₂)

private
  module SP = HasProducts (Setoid-products ℓ ℓ)
  module ST = HasTerminal (Setoid-terminal ℓ ℓ)

-- record Dinatural (F G : Functor (product 𝒞 𝒞.opposite) (SetoidCat ℓ ℓ)) : Set ℓ where
--   field
--     dtransf   : ∀ x → F .fobj (x , x) ⇒s G .fobj (x , x)
--     dinatural : ∀ {x₁ x₂} (f : x₁ 𝒞.⇒ x₂) → ((G .fmor (f , 𝒞.id _) ∘S dtransf x₁) ∘S F .fmor (𝒞.id _ , f)) ≈s ((G .fmor (𝒞.id _ , f) ∘S dtransf x₂) ∘S F .fmor (f , 𝒞.id _))

-- A Cowedge is a Dinatural transformation to a constant
record Cowedge (Y : Setoid ℓ ℓ) (F : Functor (product 𝒞 𝒞.opposite) (SetoidCat ℓ ℓ)) (X : Setoid ℓ ℓ) : Set ℓ where
  field
    dtransf   : ∀ y → (Y ×s (F .fobj (y , y))) ⇒s X
    dinatural : ∀ {y₁ y₂} (f : y₁ 𝒞.⇒ y₂) → (dtransf y₁ ∘S SP.prod-m (idS _) (F .fmor (𝒞.id _ , f))) ≈s (dtransf y₂ ∘S SP.prod-m (idS _) (F .fmor (f , 𝒞.id _)))
open Cowedge

record _≈cw_ {F : Functor (product 𝒞 𝒞.opposite) (SetoidCat ℓ ℓ)} {Y X : Setoid ℓ ℓ} (f g : Cowedge Y F X) : Set ℓ where
  field
    ≈cw≈ : ∀ y → f .dtransf y ≈s g .dtransf y
open _≈cw_

_∘cw_ : ∀ {F Z X Y} → X ⇒s Y → Cowedge Z F X → Cowedge Z F Y
(f ∘cw g) .dtransf y = f ∘S (g .dtransf y)
_∘cw_ {F} f g .dinatural {y₁}{y₂} h = begin
    (f ∘S g .dtransf y₁) ∘S SP.prod-m (idS _) (F .fmor (𝒞.id y₁ , h))
  ≈⟨ prop-setoid.assoc _ _ _ ⟩
    f ∘S (g .dtransf y₁ ∘S SP.prod-m (idS _) (F .fmor (𝒞.id y₁ , h)))
  ≈⟨ prop-setoid.∘S-cong (prop-setoid.≃m-isEquivalence .refl) (g .dinatural h) ⟩
    f ∘S (g .dtransf y₂ ∘S SP.prod-m (idS _) (F .fmor (h , 𝒞.id y₂)))
  ≈˘⟨ prop-setoid.assoc _ _ _ ⟩
    (f ∘S g .dtransf y₂) ∘S SP.prod-m (idS _) (F .fmor (h , 𝒞.id y₂))
  ∎
  where open ≈-Reasoning prop-setoid.≃m-isEquivalence

record Coend (F : Functor (product 𝒞 𝒞.opposite) (SetoidCat ℓ ℓ)) : Set (suc ℓ) where
  field
    coend-obj : Setoid ℓ ℓ
    coend-inj : Cowedge ST.witness F coend-obj
    coend-ext : ∀ {X Z} → Cowedge X F Z → (X ×s coend-obj) ⇒s Z
    coend-ext-cong : ∀ {X Z} {f g : Cowedge X F Z} → f ≈cw g → coend-ext f ≈s coend-ext g
    coend-eq  : ∀ {X Z} {f : Cowedge X F Z} {x} → f .dtransf x ≈s (coend-ext f ∘S SP.prod-m (idS X) (coend-inj .dtransf x ∘S SP.pair ST.to-terminal (idS _)))
    coend-uni : ∀ {X Z} {f : Cowedge X F Z} {h : (X ×s coend-obj) ⇒s Z} →
                (∀ x → f .dtransf x ≈s (h ∘S SP.prod-m (idS X) (coend-inj .dtransf x ∘S SP.pair ST.to-terminal (idS _)))) →
                h ≈s coend-ext f
  -- coend-natural : ∀ {Z Z'} {h : Z ⇒s Z'} {α : Cowedge F Z} → (h ∘S coend-ext α) ≈s coend-ext (h ∘cw α)
  -- coend-natural {Z} {Z'} {h} {α} = coend-uni eq
  --   where eq : (x : 𝒞.obj) → (h ∘S α .dtransf x) ≈s ((h ∘S coend-ext α) ∘S coend-inj .dtransf x)
  --         eq x = begin
  --                   h ∘S α .dtransf x                           ≈⟨ prop-setoid.∘S-cong (prop-setoid.≃m-isEquivalence .refl) coend-eq ⟩
  --                   h ∘S (coend-ext α ∘S coend-inj .dtransf x)  ≈˘⟨ prop-setoid.assoc _ _ _ ⟩
  --                   (h ∘S coend-ext α) ∘S coend-inj .dtransf x  ∎
  --                 where open ≈-Reasoning prop-setoid.≃m-isEquivalence
open Coend



------------------------------------------------------------------------------
-- Lifting EndoFunctors

import cartesian-monoidal (SetoidCat ℓ ℓ) (Setoid-terminal ℓ ℓ) (Setoid-products ℓ ℓ) as SM
open import monoidal-product

module UnaryDay (M : Functor 𝒞 𝒞) where

  -- This is really the coend ∫ʸ 𝒞(x,My) × Fy
  --
  -- There is a dinatural transformation in : 𝒞(x,My) × Fy ⇒ ∫ʸ 𝒞(x,My) × Fy
  --
  -- dinatural:
  --
  -- It has the universal property that for any other f : 𝒞(x,My) × Fy ⇒ X, there is a unique h : ∫ʸ 𝒞(x,My) × Fy ⇒ X, making h ∘ in = f
  --
  -- This can then be used to define the other parts, such as naturality.
  --
  -- Start by postulating the existence, and then using that

  -- FIXME: generalise to n-ary M.

  -- Maybe an arbitrary functor 𝒞 × 𝒞op → Setoid?

  -- FIXME: construction of coends in Setoid

  -- Now construct the lifting of a functor using coends

  M-hat-F : (F : PSh .Category.obj) (x : 𝒞.obj) → Functor (product 𝒞 𝒞.opposite) (SetoidCat ℓ ℓ)
  M-hat-F F x = MonoidalProduct.⊗-functor SM.×-monoidal ∘F pairF ((atObj x ∘F (よ ∘F M)) ∘F project₁) (F ∘F project₂)

{-
  postulate
    M-hat-obj : (F : PSh .Category.obj) (x : 𝒞.obj) → Coend (M-hat-F F x)

  M-hat-mor-cowedge : ∀ (F : PSh .Category.obj) {x y} (f : x 𝒞.⇒ y) → Cowedge (M-hat-F F y) (M-hat-obj F x .coend-obj)
  M-hat-mor-cowedge F f .dtransf z = M-hat-obj F _ .coend-inj .dtransf z ∘S HasProducts.prod-m (Setoid-products ℓ ℓ) (𝒞.precompose f ) (idS _)
  M-hat-mor-cowedge F f .dinatural g = {!!}

  -- M-hat-mor-cowedge-cong

  M-hat-mor-cowedge-id : ∀ (F : PSh .Category.obj) {x} → M-hat-mor-cowedge F (𝒞.id x) ≈cw M-hat-obj F x .coend-inj
  M-hat-mor-cowedge-id F .≈cw≈ y = begin
      M-hat-obj F _ .coend-inj .dtransf y ∘S HasProducts.prod-m (Setoid-products ℓ ℓ) (𝒞.precompose (𝒞.id _)) (idS (F .fobj y))
    ≈⟨ prop-setoid.∘S-cong (prop-setoid.≃m-isEquivalence .refl) (HasProducts.prod-m-cong (Setoid-products ℓ ℓ) {!!} (prop-setoid.≃m-isEquivalence .refl)) ⟩
      M-hat-obj F _ .coend-inj .dtransf y ∘S HasProducts.prod-m (Setoid-products ℓ ℓ) (idS _) (idS (F .fobj y))
    ≈⟨ prop-setoid.∘S-cong (prop-setoid.≃m-isEquivalence .refl) (HasProducts.prod-m-id (Setoid-products ℓ ℓ)) ⟩
      M-hat-obj F _ .coend-inj .dtransf y ∘S idS _
    ≈⟨ prop-setoid.id-right ⟩
      M-hat-obj F _ .coend-inj .dtransf y
    ∎
    where open ≈-Reasoning prop-setoid.≃m-isEquivalence

  M-hat-mor : ∀ (F : PSh .Category.obj) {x y} (f : x 𝒞.⇒ y) → M-hat-obj F y .coend-obj ⇒s M-hat-obj F x .coend-obj
  M-hat-mor F {x} {y} f = M-hat-obj F y .coend-ext (M-hat-mor-cowedge F f)

  M-hat-PSh : (F : PSh .Category.obj) → PSh .Category.obj
  M-hat-PSh F .fobj x = M-hat-obj F x .coend-obj
  M-hat-PSh F .fmor {x} {y} f = M-hat-mor F f
  M-hat-PSh F .fmor-cong f₁≈f₂ = M-hat-obj F _ .coend-ext-cong {!!}
  M-hat-PSh F .fmor-id {x} = begin
      M-hat-mor F (Category.id 𝒞.opposite x)
    ≡⟨⟩
      M-hat-obj F x .coend-ext (M-hat-mor-cowedge F (𝒞.id x))
    ≈⟨ M-hat-obj F x .coend-ext-cong (M-hat-mor-cowedge-id F) ⟩
      M-hat-obj F x .coend-ext (M-hat-obj F x .coend-inj)
    ≈˘⟨ M-hat-obj F x .coend-uni (λ w → prop-setoid.≃m-isEquivalence .sym prop-setoid.id-left) ⟩
      idS (M-hat-obj F x .coend-obj)
    ∎
    where open ≈-Reasoning prop-setoid.≃m-isEquivalence
  M-hat-PSh F .fmor-comp {x}{y}{z} f g = begin
      M-hat-obj F x .coend-ext (M-hat-mor-cowedge F (g 𝒞.∘ f))
    ≈⟨ M-hat-obj F x .coend-ext-cong {!!} ⟩
      M-hat-obj F x .coend-ext (M-hat-obj F y .coend-ext (M-hat-mor-cowedge F f) ∘cw M-hat-mor-cowedge F g)
    ≈˘⟨ coend-natural (M-hat-obj F x) ⟩
      M-hat-obj F y .coend-ext (M-hat-mor-cowedge F f) ∘S M-hat-obj F x .coend-ext (M-hat-mor-cowedge F g)
    ∎
    where open ≈-Reasoning prop-setoid.≃m-isEquivalence

  M-hat : Functor PSh PSh
  M-hat .fobj = M-hat-PSh
  M-hat .fmor {F} {G} α .transf x = M-hat-obj F x .coend-ext {!!}
  M-hat .fmor {F} {G} α .natural = {!!}
  M-hat .fmor-cong = {!!}
  M-hat .fmor-id = {!!}
  M-hat .fmor-comp = {!!}
-}

  M-hat-carrier : (F : PSh .Category.obj) → 𝒞.obj → Set ℓ
  M-hat-carrier F x = Σ[ y ∈ _ ] (x 𝒞.⇒ M .fobj y ×S F .fobj y .Carrier)

  data M-hat-eq {F} {x} : M-hat-carrier F x → M-hat-carrier F x → Set ℓ where
    eq-stop : ∀ a → M-hat-eq {F} a a
    eq-step : ∀ {y₁ f₁ Fy₁ y₂ f₂ Fy₂ y c} {Fy : F .fobj y .Carrier} →
          (h₁ : y₁ 𝒞.⇒ y) →
          (h₂ : y₂ 𝒞.⇒ y) →
          M .fmor h₁ 𝒞.∘ f₁ 𝒞.≈ M .fmor h₂ 𝒞.∘ f₂ →
          F .fobj y₁ ._≈_ (F .fmor h₁ .func Fy) Fy₁ →
          F .fobj y₂ ._≈_ (F .fmor h₂ .func Fy) Fy₂ →
          M-hat-eq {F} (y₂ , f₂ , Fy₂) c →
          M-hat-eq (y₁ , f₁ , Fy₁) c

  eq-trans : ∀ {F x a b c} → M-hat-eq {F} {x} a b → M-hat-eq {F} {x} b c → M-hat-eq {F} {x} a c
  eq-trans (eq-stop a) eq₂ = eq₂
  eq-trans (eq-step h₁ h₂ x x₁ x₂ eq₁) eq₂ = eq-step h₁ h₂ x x₁ x₂ (eq-trans eq₁ eq₂)

  eq-revtrans : ∀ {F x a b c} → M-hat-eq {F} {x} a b → M-hat-eq {F} {x} a c → M-hat-eq {F} {x} b c
  eq-revtrans (eq-stop a) eq₂ = eq₂
  eq-revtrans (eq-step h₁ h₂ x x₁ x₂ eq₁) eq₂ = eq-revtrans eq₁ (eq-step h₂ h₁ (sym 𝒞.isEquiv x) x₂ x₁ eq₂)

  eq-sym : ∀ {F x a b} → M-hat-eq {F} {x} a b → M-hat-eq {F} {x} b a
  eq-sym eq = eq-revtrans eq (eq-stop _)

  M-hat-setoid : (F : PSh .Category.obj) → 𝒞.obj → Setoid ℓ ℓ
  M-hat-setoid F x .Carrier = M-hat-carrier F x
  M-hat-setoid F x ._≈_ a b = LiftS ℓ (M-hat-eq {F} a b)
  M-hat-setoid F x .isEquivalence .refl {y , f , Fy} = liftS (eq-stop (y , f , Fy))
  M-hat-setoid F x .isEquivalence .sym (liftS eq) = liftS (eq-sym eq)
  M-hat-setoid F x .isEquivalence .trans (liftS eq₁) (liftS eq₂) = liftS (eq-trans eq₁ eq₂)

  {----------------------------------------------------------------------------------------------------}
  {- M-hat-setoid is actually the coend object -}

  M-hat-coend-inj : (F : PSh .Category.obj) (x : 𝒞.obj) → Cowedge ST.witness (M-hat-F F x) (M-hat-setoid F x)
  M-hat-coend-inj F x .dtransf y .func (lift _ , (lift f , Fy)) = y , f , Fy
  M-hat-coend-inj F x .dtransf y .func-resp-≈ {_ , lift f₁ , Fy₁} {_ , lift f₂ , Fy₂} (_ , lift f₁≈f₂ , Fy₁≈Fy₂) =
    liftS (eq-step (𝒞.id y) (𝒞.id y) (𝒞.∘-cong 𝒞.≈-refl f₁≈f₂) (F .fmor-id .func-eq (F .fobj y .refl)) (F .fmor-id .func-eq Fy₁≈Fy₂) (eq-stop _))
  M-hat-coend-inj F x .dinatural {y₁} {y₂} f .func-eq (_ , lift g₁≈g₂ , Fy₂≈Fy₂') =
    liftS (eq-step f (𝒞.id _) (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong (M .fmor-id) 𝒞.≈-refl)) (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl 𝒞.id-left) (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl g₁≈g₂) (𝒞.≈-trans (𝒞.≈-sym 𝒞.id-left) (𝒞.∘-cong (𝒞.≈-sym (M .fmor-id)) 𝒞.≈-refl)))))
      (F .fmor f .func-resp-≈ (F .fobj _ .sym Fy₂≈Fy₂')) (F .fmor (𝒞.id _) .func-resp-≈ (F .fobj _ .refl)) (eq-stop _))

  M-hat-coend : (F : PSh .Category.obj) (x : 𝒞.obj) → Coend (M-hat-F F x)
  M-hat-coend F x .coend-obj = M-hat-setoid F x
  M-hat-coend F x .coend-inj = M-hat-coend-inj F x
  M-hat-coend F x .coend-ext α .func (p , (z , g , Fz)) = α .dtransf z .func (p , lift g , Fz)
  M-hat-coend F x .coend-ext {P} {Z} α .func-resp-≈ {p₁ , z₁ , g₁ , Fz₁} {p₂ , z₂ , g₂ , Fz₂} (p₁≈p₂ , liftS eq) = resp-≈ eq
    where resp-≈ : ∀ {z₁ g₁ Fz₁ z₂ g₂ Fz₂} → M-hat-eq (z₁ , g₁ , Fz₁) (z₂ , g₂ , Fz₂) → Z ._≈_ (α .dtransf z₁ .func (p₁ , lift g₁ , Fz₁)) (α .dtransf z₂ .func (p₂ , lift g₂ , Fz₂))
          resp-≈ (eq-stop a) = α .dtransf _ .func-resp-≈ (p₁≈p₂ , lift 𝒞.≈-refl , F .fobj _ .refl)
          resp-≈ {z₁}{g₁}{Fz₁}{z₂}{g₂}{Fz₂} (eq-step {y = y} {Fy = Fy} h₁ h₂ x x₁ x₂ eq) =
            Z .trans (α .dtransf z₁ .func-resp-≈ (P .refl , lift (𝒞.≈-sym (𝒞.≈-trans (𝒞.∘-cong (M .fmor-id) 𝒞.≈-refl) 𝒞.id-left)) , F .fobj z₁ .sym x₁))
           (Z .trans (α .dinatural h₁ .func-eq (P .refl , M-hat-F F _ .fobj _ .refl))
           (Z .trans (α .dtransf y .func-resp-≈ (P .refl , lift x , F .fobj _ .refl))
           (Z .trans (Z .sym (α .dinatural h₂ .func-eq (P .refl , M-hat-F F _ .fobj _ .refl)))
           (Z .trans (α .dtransf _ .func-resp-≈ (P .refl , lift (𝒞.≈-trans (𝒞.∘-cong (M .fmor-id) 𝒞.≈-refl) 𝒞.id-left) , x₂))
                     (resp-≈ eq)))))
  M-hat-coend F x .coend-ext-cong {P} {Z} {α} {β} α≈β = mk-≈s λ { (p , y , f , Fy) → α≈β .≈cw≈ y .func-eq (P .refl , lift 𝒞.≈-refl , F .fobj _ .refl) }
  M-hat-coend F x .coend-eq {P} {Z} {α} {y} = mk-≈s λ { (p , lift f , Fy) → Z .refl }
  M-hat-coend F x .coend-uni {P} {Z} {α} {h} h-property = mk-≈s (λ { (p , y , f , Fy) → Z .sym (h-property y .func-eq (P .refl , lift 𝒞.≈-refl , F .fobj _ .refl)) })

  {------------------------------------------------------------------------------}

  M-hat-mor : ∀ (F : PSh .Category.obj) {x y} (f : x 𝒞.⇒ y) → M-hat-setoid F y ⇒s M-hat-setoid F x
  M-hat-mor F f .func (z , g , Fz) = z , g 𝒞.∘ f , Fz
  M-hat-mor F f .func-resp-≈ (liftS eq) = liftS (resp-≈ eq)
    where resp-≈ : ∀ {z₁ g₁ Fz₁ z₂ g₂ Fz₂} → M-hat-eq {F} (z₁ , g₁ , Fz₁) (z₂ , g₂ , Fz₂) → M-hat-eq {F} (z₁ , g₁ 𝒞.∘ f , Fz₁) (z₂ , g₂ 𝒞.∘ f , Fz₂)
          resp-≈ (eq-stop a) = eq-stop (_ , _ 𝒞.∘ f , _)
          resp-≈ (eq-step h₁ h₂ x x₁ x₂ eq) = eq-step h₁ h₂ (𝒞.≈-trans (𝒞.≈-sym (𝒞.assoc _ _ _)) (𝒞.≈-trans (𝒞.∘-cong x 𝒞.≈-refl) (𝒞.assoc _ _ _))) x₁ x₂ (resp-≈ eq)

  M-hat-PSh : PSh .Category.obj → PSh .Category.obj
  M-hat-PSh F .fobj = M-hat-setoid F
  M-hat-PSh F .fmor = M-hat-mor F
  M-hat-PSh F .fmor-cong {x} {y} f₁≈f₂ =
    mk-≈s (λ (z , f , Fz) → liftS (eq-step (𝒞.id z) (𝒞.id z) (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong 𝒞.≈-refl f₁≈f₂)) (F .fmor-id .func-eq (F .fobj _ .refl)) (F .fmor-id .func-eq (F .fobj _ .refl)) (eq-stop _)))
  M-hat-PSh F .fmor-id = mk-≈s (λ (z , f , Fz) → liftS (eq-step (𝒞.id z) (𝒞.id z) (𝒞.∘-cong 𝒞.≈-refl 𝒞.id-right) (F .fmor-id .func-eq (F .fobj _ .refl)) (F .fmor-id .func-eq (F .fobj _ .refl)) (eq-stop _)))
  M-hat-PSh F .fmor-comp f g = mk-≈s (λ (z , h , Fz) → liftS (eq-step (𝒞.id z) (𝒞.id z) (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-sym (𝒞.assoc h g f))) (F .fmor-id .func-eq (F .fobj _ .refl)) (F .fmor-id .func-eq (F .fobj _ .refl)) (eq-stop _)))

  M-hat-nat : (F G : PSh .Category.obj) → NatTrans F G → NatTrans (M-hat-PSh F) (M-hat-PSh G)
  M-hat-nat F G α .transf x .func (z , g , Fz) = z , g , α .transf z .func Fz
  M-hat-nat F G α .transf x .func-resp-≈ (liftS eq) = liftS (resp-≈ eq)
    where
      resp-≈ : ∀ {z₁ g₁ Fz₁ z₂ g₂ Fz₂} → M-hat-eq {F} {x} (z₁ , g₁ , Fz₁) (z₂ , g₂ , Fz₂) → M-hat-eq {G} (z₁ , g₁ , α .transf _ .func Fz₁) (z₂ , g₂ , α .transf _ .func Fz₂)
      resp-≈ (eq-step h₁ h₂ eq₁ eq₂ eq₃ eq) =
        eq-step h₁ h₂ eq₁ (G .fobj _ .trans (α .natural h₁ .func-eq (F .fobj _ .refl)) (α .transf _ .func-resp-≈ eq₂))
                          (G .fobj _ .trans (α .natural h₂ .func-eq (F .fobj _ .refl)) (α .transf _ .func-resp-≈ eq₃))
                          (resp-≈ eq)
      resp-≈ (eq-stop x) = eq-stop (_ , _ , α .transf _ .func _)
  M-hat-nat F G α .natural {x} {y} f = mk-≈s help
    where help : ((z , g , Fz) : Carrier (M-hat-setoid F x)) →  LiftS ℓ (M-hat-eq (z , g 𝒞.∘ f , α .transf z .func Fz) (z , g 𝒞.∘ f , α .transf z .func Fz))
          help (z , g , Fz) = liftS (eq-stop _)

  M-hat : Functor PSh PSh
  M-hat .fobj = M-hat-PSh
  M-hat .fmor {F} {G} α = M-hat-nat F G α
  M-hat .fmor-cong {F} {G} α₁≈α₂ .transf-eq x =
    mk-≈s (λ { (z , g , Fz) → liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl
                                          (G .fmor-id .func-eq (G .fobj z .sym (α₁≈α₂ .transf-eq _ .func-eq (F .fobj z .refl))))
                                          (G .fmor-id .func-eq (refl (isEquivalence (G .fobj z)))) (eq-stop _)) })
  M-hat .fmor-id {F} .transf-eq x =
    mk-≈s λ { (z , g , Fz) → liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl (F .fmor-id .func-eq (F .fobj z .refl)) (F .fmor-id .func-eq (F .fobj _ .refl)) (eq-stop _)) }
  M-hat .fmor-comp {F} {G} {H} α β .transf-eq x =
    mk-≈s λ { (z , g , Fz) → liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl (H .fmor-id .func-eq (H .fobj z .refl)) (H .fmor-id .func-eq (H .fobj _ .refl)) (eq-stop _)) }

  ------------------------------------------------------------------------------
  -- Yoneda embedding preserves the functor
  yoneda-preserve-M : NatTrans (よ ∘F M) (M-hat ∘F よ)
  yoneda-preserve-M .transf x .transf y .func (lift f) = x , f , lift (𝒞.id _)
  yoneda-preserve-M .transf x .transf y .func-resp-≈ {lift f₁} {lift f₂} (lift f₁≈f₂) =
    liftS (eq-step (𝒞.id _) (𝒞.id _) (𝒞.∘-cong 𝒞.≈-refl f₁≈f₂) (lift 𝒞.id-left) (lift 𝒞.id-left) (eq-stop _))
  yoneda-preserve-M .transf x .natural g = mk-≈s λ (lift f) →
    liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl (lift 𝒞.id-left) (lift 𝒞.id-left) (eq-stop _))
  yoneda-preserve-M .natural {x₁}{x₂} g .transf-eq y = mk-≈s λ (lift f) →
    liftS (eq-step g (𝒞.id _) (𝒞.≈-trans (𝒞.≈-sym 𝒞.id-left) (𝒞.≈-sym (𝒞.∘-cong (M .fmor-id) 𝒞.≈-refl))) (lift 𝒞.id-swap) (lift 𝒞.id-left) (eq-stop _))

  yoneda-preserve-M⁻¹-cw : ∀ x y → Cowedge prop-setoid.𝟙 (M-hat-F (よ₀ x) y) (𝒞.hom-setoid-l ℓ ℓ y (M .fobj x))
  yoneda-preserve-M⁻¹-cw x y .dtransf z .func (_ , lift f , lift g) = lift (M .fmor g 𝒞.∘ f)
  yoneda-preserve-M⁻¹-cw x y .dtransf z .func-resp-≈ {_ , lift f₁ , lift g₁} {_ , lift f₂ , lift g₂} (_ , lift f₁≈f₂ , lift g₁≈g₂) = lift (𝒞.∘-cong (M .fmor-cong g₁≈g₂) f₁≈f₂)
  yoneda-preserve-M⁻¹-cw x y .dinatural {z₁}{z₂} h = mk-≈s λ (_ , lift f , lift g) →
    lift (begin
      M .fmor (g 𝒞.∘ h) 𝒞.∘ (M .fmor (𝒞.id z₁) 𝒞.∘ f)
    ≈⟨ 𝒞.∘-cong (M .fmor-comp _ _) (𝒞.∘-cong (M .fmor-id) 𝒞.≈-refl) ⟩
      (M .fmor g 𝒞.∘ M .fmor h) 𝒞.∘ (𝒞.id _ 𝒞.∘ f)
    ≈⟨ 𝒞.∘-cong (𝒞.∘-cong (M .fmor-cong (𝒞.≈-sym 𝒞.id-right)) 𝒞.≈-refl) 𝒞.id-left ⟩
      (M .fmor (g 𝒞.∘ 𝒞.id _) 𝒞.∘ M .fmor h) 𝒞.∘ f
    ≈⟨ 𝒞.assoc _ _ _ ⟩
      M .fmor (g 𝒞.∘ 𝒞.id z₂) 𝒞.∘ (M .fmor h 𝒞.∘ f)
    ∎)
    where open ≈-Reasoning 𝒞.isEquiv

  yoneda-preserve-M⁻¹ : NatTrans (M-hat ∘F よ) (よ ∘F M)
  yoneda-preserve-M⁻¹ .transf x .transf y = M-hat-coend _ _ .coend-ext (yoneda-preserve-M⁻¹-cw x y) ∘S SM.×-lunit⁻¹
  yoneda-preserve-M⁻¹ .transf x .natural {y₁}{y₂} f = mk-≈s λ (z , g , lift h) →
    lift (𝒞.assoc _ _ _)
  yoneda-preserve-M⁻¹ .natural {x₁} {x₂} f .transf-eq x = mk-≈s λ (z , g , lift h) →
    lift (𝒞.≈-trans (𝒞.≈-sym (𝒞.assoc _ _ _)) (𝒞.∘-cong (𝒞.≈-sym (M .fmor-comp _ _)) 𝒞.≈-refl))

------------------------------------------------------------------------------
module DayMonad (M : Monad 𝒞) where

  open Monad M renaming (funct to Mfunct)

  open UnaryDay Mfunct

  unit-hat : NatTrans Id M-hat
  unit-hat .transf F .transf x .func Fx = x , unit .transf x , Fx
  unit-hat .transf F .transf x .func-resp-≈ {Fx₁} {Fx₂} Fx₁≈Fx₂ =
    liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl (F .fmor-id .func-eq (F .fobj x .sym Fx₁≈Fx₂)) (F .fmor-id .func-eq (F .fobj _ .refl)) (eq-stop _))
  unit-hat .transf F .natural f .func-eq x₁≈x₂ =
    liftS (eq-step (𝒞.id _) f
                (𝒞.≈-trans (𝒞.∘-cong (Mfunct .fmor-id) 𝒞.≈-refl) (𝒞.≈-trans 𝒞.id-left (𝒞.≈-sym (unit .natural f))))
                (F .fmor-id .func-eq (F .fobj _ .refl))
                (F .fmor f .func-resp-≈ x₁≈x₂) (eq-stop _))
  unit-hat .natural {F}{G} α .transf-eq x .func-eq {x₁}{x₂} x₁≈x₂ =
    liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl (G .fmor-id .func-eq (α .transf x .func-resp-≈ (F .fobj x .sym x₁≈x₂))) (G .fmor-id .func-eq (G .fobj _ .refl)) (eq-stop _))

  join-cw-inner : ∀ F x y → Cowedge (𝒞.hom-setoid-l ℓ ℓ x (Mfunct .fobj y)) (M-hat-F F y) (M-hat-setoid F x)
  join-cw-inner F x y .dtransf z .func (lift f , lift g , Fz) = z , join .transf z 𝒞.∘ (Mfunct .fmor g 𝒞.∘ f) , Fz
  join-cw-inner F x y .dtransf z .func-resp-≈ (lift f₁≈f₂ , lift g₁≈g₂ , Fz₁≈Fz₂) =
    liftS (eq-step (𝒞.id _) (𝒞.id _) (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong (Mfunct .fmor-cong g₁≈g₂) f₁≈f₂))) (F .fmor-id .func-eq (F .fobj z .refl)) (F .fmor-id .func-eq Fz₁≈Fz₂) (eq-stop _))
  join-cw-inner F x y .dinatural {y₁} {y₂} h =
    mk-≈s λ (lift f , lift g , Fy₂) → liftS (eq-step h (𝒞.id _)
                                                     (begin
                                                       Mfunct .fmor h 𝒞.∘ (join .transf y₁ 𝒞.∘ (Mfunct .fmor (Mfunct .fmor (𝒞.id y₁) 𝒞.∘ g) 𝒞.∘ f))
                                                     ≈˘⟨ 𝒞.assoc _ _ _ ⟩
                                                       (Mfunct .fmor h 𝒞.∘ join .transf y₁) 𝒞.∘ (Mfunct .fmor (Mfunct .fmor (𝒞.id y₁) 𝒞.∘ g) 𝒞.∘ f)
                                                     ≈⟨ 𝒞.∘-cong (join .natural h) (𝒞.∘-cong (Mfunct .fmor-cong (𝒞.∘-cong (Mfunct .fmor-id) 𝒞.≈-refl)) 𝒞.≈-refl) ⟩
                                                       (join .transf y₂ 𝒞.∘ Mfunct .fmor (Mfunct .fmor h)) 𝒞.∘ (Mfunct .fmor (𝒞.id _ 𝒞.∘ g) 𝒞.∘ f)
                                                     ≈⟨ 𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong (Mfunct .fmor-cong 𝒞.id-left) 𝒞.≈-refl) ⟩
                                                       (join .transf y₂ 𝒞.∘ Mfunct .fmor (Mfunct .fmor h)) 𝒞.∘ (Mfunct .fmor g 𝒞.∘ f)
                                                     ≈⟨ 𝒞.assoc _ _ _ ⟩
                                                       join .transf y₂ 𝒞.∘ (Mfunct .fmor (Mfunct .fmor h) 𝒞.∘ (Mfunct .fmor g 𝒞.∘ f))
                                                     ≈˘⟨ 𝒞.∘-cong 𝒞.id-left (𝒞.assoc _ _ _) ⟩
                                                       (𝒞.id _ 𝒞.∘ join .transf y₂) 𝒞.∘ ((Mfunct .fmor (Mfunct .fmor h) 𝒞.∘ Mfunct .fmor g) 𝒞.∘ f)
                                                     ≈˘⟨ 𝒞.∘-cong (𝒞.∘-cong (Mfunct .fmor-id) 𝒞.≈-refl) (𝒞.∘-cong (Mfunct .fmor-comp _ _) 𝒞.≈-refl) ⟩
                                                       (Mfunct .fmor (𝒞.id _) 𝒞.∘ join .transf y₂) 𝒞.∘ (Mfunct .fmor (Mfunct .fmor h 𝒞.∘ g) 𝒞.∘ f)
                                                     ≈⟨ 𝒞.assoc _ _ _ ⟩
                                                       Mfunct .fmor (𝒞.id y₂) 𝒞.∘ (join .transf y₂ 𝒞.∘ (Mfunct .fmor (Mfunct .fmor h 𝒞.∘ g) 𝒞.∘ f))
                                                     ∎)
                                                     (F .fobj y₁ .refl) (F .fobj y₂ .refl) (eq-stop _))
    where open ≈-Reasoning 𝒞.isEquiv

  join-cw : ∀ F x → Cowedge prop-setoid.𝟙 (M-hat-F (M-hat-PSh F) x) (M-hat-setoid F x)
  join-cw F x .dtransf y = M-hat-coend F y .coend-ext (join-cw-inner F x y) ∘S SM.×-lunit
  join-cw F x .dinatural {y₁} {y₂} h = mk-≈s λ (lift _ , lift f , z , g , Fz) →
    liftS (eq-step (𝒞.id _) (𝒞.id _) (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-trans (𝒞.∘-cong (Mfunct .fmor-comp _ _) (𝒞.∘-cong (Mfunct .fmor-id) 𝒞.≈-refl)) (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl 𝒞.id-left) (𝒞.≈-trans (𝒞.assoc _ _ _) (𝒞.∘-cong (Mfunct .fmor-cong (𝒞.≈-sym 𝒞.id-right)) 𝒞.≈-refl)))))) (F .fmor-id .func-eq (F .fobj _ .refl)) (F .fmor-id .func-eq (F .fobj _ .refl)) (eq-stop _))

  join-hat : NatTrans (M-hat ∘F M-hat) M-hat
  join-hat .transf F .transf x = M-hat-coend (M-hat-PSh F) x .coend-ext (join-cw F x) ∘S SM.×-lunit⁻¹
  join-hat .transf F .natural {x₂} {x₁} f = mk-≈s λ { (y , f , z , g , Fz) → liftS (eq-step (𝒞.id _) (𝒞.id _) (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-trans (𝒞.assoc _ _ _) (𝒞.∘-cong 𝒞.≈-refl (𝒞.assoc _ _ _)))) (F .fmor-id .func-eq (F .fobj _ .refl)) (F .fmor-id .func-eq (F .fobj _ .refl)) (eq-stop _)) }
  join-hat .natural {F} {G} α .transf-eq x = mk-≈s λ (y , f , z , g , Fz) → liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl (G .fobj z .trans (α .natural (𝒞.id _) .func-eq (F .fobj _ .refl)) (α .transf z .func-resp-≈ (F .fmor-id .func-eq (F .fobj _ .refl)))) (G .fobj _ .trans (α .natural (𝒞.id _) .func-eq (F .fobj _ .refl)) (α .transf z .func-resp-≈ (F .fmor-id .func-eq (F .fobj _ .refl)))) (eq-stop _))

  monad-hat : Monad PSh
  monad-hat .Monad.funct = M-hat
  monad-hat .Monad.unit = unit-hat
  monad-hat .Monad.join = join-hat

  module _ (𝒞P : HasProducts 𝒞) (str : ∀ {x y} → 𝒞P .HasProducts.prod x (Mfunct .fobj y) 𝒞.⇒ Mfunct .fobj (𝒞P .HasProducts.prod x y)) where

    module 𝒞P = HasProducts 𝒞P
    open MonoidalProduct
    import cartesian-monoidal _ terminal products as PShM

{-
    strength-cw : ∀ F G x → Cowedge (F .fobj x) (M-hat-F G x) (M-hat-setoid ((PShM.×-monoidal ⊗ F) G) x)
    strength-cw F G x .dtransf y .func (Fx , lift f , Gy) = 𝒞P.prod x y , (str 𝒞.∘ 𝒞P.pair (𝒞.id _) f) , (F .fmor 𝒞P.p₁ .func Fx) , (G .fmor 𝒞P.p₂ .func Gy)
    strength-cw F G x .dtransf y .func-resp-≈ (Fx₁≈Fx₂ , lift f₁≈f₂ , Gy₁≈Gy₂) =
      liftS (eq-step (𝒞.id _) (𝒞.id _) (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong 𝒞.≈-refl (𝒞P.pair-cong 𝒞.≈-refl f₁≈f₂)))
                     ((F .fobj _ .trans (F .fmor-id .func-eq (F .fobj _ .refl)) (F .fmor 𝒞P.p₁ .func-resp-≈ (F .fobj _ .sym Fx₁≈Fx₂))) , G .fobj _ .trans (G .fmor-id .func-eq (G .fobj _ .refl)) (G .fmor 𝒞P.p₂ .func-resp-≈ (G .fobj _ .sym Gy₁≈Gy₂)))
                     ((F .fmor-id .func-eq (F .fobj _ .refl)) , G .fmor-id .func-eq (G .fobj _ .refl))
                     (eq-stop _))
    strength-cw F G x .dinatural {y₁} {y₂} f = mk-≈s λ (Fx , lift g , Gy₂) →
      liftS (eq-step (𝒞P.prod-m (𝒞.id _) f) (𝒞.id _)
                     {!!}
                     (F .fobj _ .trans (F .fobj _ .sym (F .fmor-comp _ _ .func-eq (F .fobj _ .refl))) (F .fobj _ .trans (F .fmor-cong (𝒞P.pair-p₁ _ _) .func-eq (F .fobj _ .refl)) (F .fmor-cong 𝒞.id-left .func-eq (F .fobj _ .refl))) ,
                      G .fobj _ .trans (G .fobj _ .sym (G .fmor-comp _ _ .func-eq (G .fobj _ .refl))) (G .fobj _ .trans (G .fmor-cong (𝒞P.pair-p₂ _ _ ) .func-eq (G .fobj _ .refl)) (G .fmor-comp _ _ .func-eq (G .fobj _ .refl))))
                     (F .fmor-id .func-eq (F .fobj _ .refl) ,
                      G .fmor-id .func-eq (G .fmor 𝒞P.p₂ .func-resp-≈ (G .fobj _ .sym (G .fmor-id .func-eq (G .fobj _ .refl)))))
                     (eq-stop _))

    strength-hat : NatTrans (⊗-functor PShM.×-monoidal ∘F pairF project₁ (M-hat ∘F project₂)) (M-hat ∘F ⊗-functor PShM.×-monoidal)
    strength-hat .transf (F , G) .transf x = M-hat-coend _ _ .coend-ext (strength-cw F G x)
    strength-hat .transf (F , G) .natural {x₂} {x₁} f = mk-≈s λ (Fx₂ , y , g , Gy) →
      liftS (eq-step (𝒞.id _) (𝒞P.prod-m f (𝒞.id _))
                     {!!}
                     ((F .fmor-id .func-eq (F .fobj _ .refl)) , (G .fmor-id .func-eq (G .fobj _ .refl)))
                     (F .fobj _ .trans (F .fobj _ .sym (F .fmor-comp _ _ .func-eq (F .fobj _ .refl))) (F .fobj _ .trans (F .fmor-cong (𝒞P.pair-p₁ _ _) .func-eq (F .fobj _ .refl)) (F .fmor-comp _ _ .func-eq (F .fobj _ .refl))) ,
                      G .fobj _ .trans (G .fobj _ .sym (G .fmor-comp _ _ .func-eq (G .fobj _ .refl))) (G .fobj _ .trans (G .fmor-cong (𝒞P.pair-p₂ _ _) .func-eq (G .fobj _ .refl)) (G .fmor-cong 𝒞.id-left .func-eq (G .fobj _ .refl))))
                     (eq-stop _))
    strength-hat .natural {F₁ , G₁} {F₂ , G₂} (α₁ , α₂) .transf-eq x = mk-≈s λ (F₁x , y , g , G₁y) →
      liftS (eq-step (𝒞.id _) (𝒞.id _) 𝒞.≈-refl
                     (F₂ .fobj _ .trans (F₂ .fmor-id .func-eq (F₂ .fobj _ .refl)) (α₁ .natural _ .func-eq (F₁ .fobj _ .refl)) , G₂ .fobj _ .trans (G₂ .fmor-id .func-eq (G₂ .fobj _ .refl)) (α₂ .natural _ .func-eq (G₁ .fobj _ .refl)))
                     (F₂ .fmor-id .func-eq (F₂ .fobj _ .refl) , G₂ .fmor-id .func-eq (G₂ .fobj _ .refl))
                     (eq-stop _))
-}
