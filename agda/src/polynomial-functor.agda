{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Level using (_⊔_)
open import categories using (Category; HasProducts; HasStrongCoproducts; coKleisli-prod)
open import prop-setoid using (module ≈-Reasoning)
open import functor using (Functor)

module polynomial-functor where

data Poly {o m e} (𝒞 : Category o m e) (n : ℕ) : Set o where
  const : Category.obj 𝒞 → Poly 𝒞 n
  var   : Fin n → Poly 𝒞 n
  _+_   : Poly 𝒞 n → Poly 𝒞 n → Poly 𝒞 n
  _×_   : Poly 𝒞 n → Poly 𝒞 n → Poly 𝒞 n
  μ     : Poly 𝒞 (suc n) → Poly 𝒞 n

extend : ∀ {n} {ℓ} {A : Set ℓ} → (Fin n → A) → A → Fin (suc n) → A
extend δ x Fin.zero    = x
extend δ x (Fin.suc i) = δ i

-- Interpretation of the polynomials with an endofunctor, strong for the products, applied at every
-- sum and product; initial algebras for the μ-polynomials, with the catamorphism in context.
module Interp
  {o m e} {𝒞 : Category o m e} (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (L : Category.obj 𝒞 → Category.obj 𝒞)
  (under : ∀ {Γ X Y} → Category._⇒_ 𝒞 (HasProducts.prod 𝒞P Γ X) Y →
                       Category._⇒_ 𝒞 (HasProducts.prod 𝒞P Γ (L X)) (L Y))
  where

  open Category 𝒞
  open HasProducts 𝒞P
  open HasStrongCoproducts 𝒞SC

  fobj : (μ-obj : ∀ {k} → Poly 𝒞 (suc k) → (Fin k → obj) → obj) → ∀ {n} → Poly 𝒞 n → (Fin n → obj) → obj
  fobj μ-obj (const A) δ = A
  fobj μ-obj (var i)   δ = δ i
  fobj μ-obj (P + Q)   δ = coprod (L (fobj μ-obj P δ)) (L (fobj μ-obj Q δ))
  fobj μ-obj (P × Q)   δ = L (prod (fobj μ-obj P δ) (fobj μ-obj Q δ))
  fobj μ-obj (μ P)     δ = μ-obj P δ

  record HasMu : Set (o ⊔ m ⊔ e) where
    field
      μ-obj : ∀ {k} → Poly 𝒞 (suc k) → (Fin k → obj) → obj
      inMap : ∀ {k} (P : Poly 𝒞 (suc k)) (δ : Fin k → obj) → fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
      ⦅_⦆   : ∀ {k} {Γ A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj} →
              prod Γ (fobj μ-obj P (extend δ A)) ⇒ A → prod Γ (μ-obj P δ) ⇒ A

    strong-extend-mor : ∀ {k} {Γ : obj} {δ δ' : Fin k → obj} {X Y : obj} →
                        (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ X ⇒ Y →
                        ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
    strong-extend-mor fs xy Fin.zero    = xy
    strong-extend-mor fs xy (Fin.suc i) = fs i

    mutual
      strong-fmor : ∀ {k} {Γ : obj} (P : Poly 𝒞 k) {δ δ' : Fin k → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (fobj μ-obj P δ) ⇒ fobj μ-obj P δ'
      strong-fmor (const A) fs = p₂
      strong-fmor (var i)   fs = fs i
      strong-fmor (P + Q)   fs = copair (in₁ ∘ under (strong-fmor P fs)) (in₂ ∘ under (strong-fmor Q fs))
      strong-fmor (P × Q)   fs = under (strong-prod-m (strong-fmor P fs) (strong-fmor Q fs))
      strong-fmor (μ P)     fs = strong-μ-fmor P fs

      strong-μ-fmor : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) {δ δ' : Fin k → obj} →
                      (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
      strong-μ-fmor P {δ} {δ'} fs = ⦅ inMap P δ' ∘ strong-fmor P (strong-extend-mor fs p₂) ⦆

  infixl 21 _∘co_
  _∘co_ : ∀ {Γ X Y Z} → prod Γ Y ⇒ Z → prod Γ X ⇒ Y → prod Γ X ⇒ Z
  f ∘co g = f ∘ pair p₁ g

  record HasMuLaws (Mu : HasMu) : Set (o ⊔ m ⊔ e) where
    open HasMu Mu
    field
      ⦅⦆-β : ∀ {k} {Γ A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) →
             (⦅ alg ⦆ ∘co (inMap P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) ⦅ alg ⦆))
      ⦅⦆-η : ∀ {k} {Γ A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) (h : prod Γ (μ-obj P δ) ⇒ A) →
             (h ∘co (inMap P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) h)) → h ≈ ⦅ alg ⦆

  -- The laws of the transport across the endofunctor: a congruence, functorial for the composition
  -- in context, and the identity on the projection.
  record UnderLaws : Set (o ⊔ m ⊔ e) where
    field
      under-cong : ∀ {Γ X Y} {f g : prod Γ X ⇒ Y} → f ≈ g → under f ≈ under g
      under-co   : ∀ {Γ X Y Z} (f : prod Γ Y ⇒ Z) (g : prod Γ X ⇒ Y) → (under f ∘co under g) ≈ under (f ∘co g)
      under-p₂   : ∀ {Γ X} → under (p₂ {Γ} {X}) ≈ p₂

  -- Consequences of the initial-algebra laws: the fold respects its algebra, fusion and reflection,
  -- and the strong action is a functor in the argument maps.
  module MuConsequences (Mu : HasMu) (Laws : HasMuLaws Mu) (UL : UnderLaws) where
    open HasMu Mu
    open HasMuLaws Laws
    open UnderLaws UL
    private module CoK {Γ : obj} = Category (coKleisli-prod 𝒞P Γ)

    ⦅⦆-cong : ∀ {k} {Γ A : obj} (P : Poly 𝒞 (suc k)) (δ : Fin k → obj)
              {alg alg' : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A} →
              alg ≈ alg' → ⦅_⦆ {P = P} {δ = δ} alg ≈ ⦅_⦆ {P = P} {δ = δ} alg'
    ⦅⦆-cong P δ {alg} {alg'} e =
      ⦅⦆-η {P = P} {δ = δ} alg' (⦅_⦆ {P = P} {δ = δ} alg)
        (≈-trans (⦅⦆-β {P = P} {δ = δ} alg) (∘-cong e ≈-refl))

    -- A plain morphism moves out of a composite in context.
    ∘co-push : ∀ {Γ W X Y Z} (x : prod Γ Y ⇒ Z) (a : X ⇒ Y) (y : prod Γ W ⇒ X) →
               ((x ∘co (a ∘ p₂)) ∘co y) ≈ (x ∘co (a ∘ y))
    ∘co-push x a y =
      begin
        (x ∘ pair p₁ (a ∘ p₂)) ∘ pair p₁ y
      ≈⟨ CoK.assoc _ _ _ ⟩
        x ∘ pair p₁ ((a ∘ p₂) ∘ pair p₁ y)
      ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _)))) ⟩
        x ∘ pair p₁ (a ∘ y)
      ∎ where open ≈-Reasoning isEquiv

    -- Composites of copairings of injections.
    copair-comp : ∀ {Γ X₁ X₂ Y₁ Y₂ Z₁ Z₂}
      (f₂ : prod Γ Y₁ ⇒ Z₁) (g₂ : prod Γ Y₂ ⇒ Z₂) (f₁ : prod Γ X₁ ⇒ Y₁) (g₁ : prod Γ X₂ ⇒ Y₂) →
      (copair (in₁ ∘ f₂) (in₂ ∘ g₂) ∘co copair (in₁ ∘ f₁) (in₂ ∘ g₁))
        ≈ copair (in₁ ∘ (f₂ ∘co f₁)) (in₂ ∘ (g₂ ∘co g₁))
    copair-comp f₂ g₂ f₁ g₁ =
      ≈-trans (≈-sym (copair-ext _)) (copair-cong branch₁ branch₂)
      where
        G = copair (in₁ ∘ f₂) (in₂ ∘ g₂)
        F = copair (in₁ ∘ f₁) (in₂ ∘ g₁)

        branch₁ : ((G ∘co F) ∘co (in₁ ∘ p₂)) ≈ (in₁ ∘ (f₂ ∘co f₁))
        branch₁ =
          begin
            (G ∘co F) ∘co (in₁ ∘ p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            G ∘co (F ∘co (in₁ ∘ p₂))
          ≈⟨ CoK.∘-cong ≈-refl (copair-in₁ _ _) ⟩
            G ∘co (in₁ ∘ f₁)
          ≈˘⟨ ∘co-push G in₁ f₁ ⟩
            (G ∘co (in₁ ∘ p₂)) ∘co f₁
          ≈⟨ CoK.∘-cong (copair-in₁ _ _) ≈-refl ⟩
            (in₁ ∘ f₂) ∘co f₁
          ≈⟨ assoc _ _ _ ⟩
            in₁ ∘ (f₂ ∘co f₁)
          ∎ where open ≈-Reasoning isEquiv

        branch₂ : ((G ∘co F) ∘co (in₂ ∘ p₂)) ≈ (in₂ ∘ (g₂ ∘co g₁))
        branch₂ =
          begin
            (G ∘co F) ∘co (in₂ ∘ p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            G ∘co (F ∘co (in₂ ∘ p₂))
          ≈⟨ CoK.∘-cong ≈-refl (copair-in₂ _ _) ⟩
            G ∘co (in₂ ∘ g₁)
          ≈˘⟨ ∘co-push G in₂ g₁ ⟩
            (G ∘co (in₂ ∘ p₂)) ∘co g₁
          ≈⟨ CoK.∘-cong (copair-in₂ _ _) ≈-refl ⟩
            (in₂ ∘ g₂) ∘co g₁
          ≈⟨ assoc _ _ _ ⟩
            in₂ ∘ (g₂ ∘co g₁)
          ∎ where open ≈-Reasoning isEquiv

    mutual
      strong-fmor-cong : ∀ {k} {Γ : obj} (P : Poly 𝒞 k) {δ δ' : Fin k → obj}
                         {fs fs' : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                         (∀ i → fs i ≈ fs' i) → strong-fmor P fs ≈ strong-fmor P fs'
      strong-fmor-cong (const A) es = ≈-refl
      strong-fmor-cong (var i)   es = es i
      strong-fmor-cong (P + Q)   es =
        copair-cong (∘-cong ≈-refl (under-cong (strong-fmor-cong P es)))
                    (∘-cong ≈-refl (under-cong (strong-fmor-cong Q es)))
      strong-fmor-cong (P × Q)   es =
        under-cong (strong-prod-m-cong (strong-fmor-cong P es) (strong-fmor-cong Q es))
      strong-fmor-cong (μ P)     es = strong-μ-fmor-cong P es

      strong-μ-fmor-cong : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) {δ δ' : Fin k → obj}
                           {fs fs' : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                           (∀ i → fs i ≈ fs' i) → strong-μ-fmor P fs ≈ strong-μ-fmor P fs'
      strong-μ-fmor-cong P {δ} {δ'} {fs} {fs'} es =
        ⦅⦆-cong P δ (∘-cong ≈-refl (strong-fmor-cong P es'))
        where
          es' : ∀ i → strong-extend-mor fs p₂ i ≈ strong-extend-mor fs' p₂ i
          es' Fin.zero    = ≈-refl
          es' (Fin.suc i) = es i

    -- Pointwise composition in context of extended environments is the extension of the composites.
    strong-extend-mor-comp : ∀ {k} {Γ : obj} {δ δ' δ'' : Fin k → obj} {X Y Z : obj}
      {as : ∀ i → prod Γ (δ' i) ⇒ δ'' i} {bs : ∀ i → prod Γ (δ i) ⇒ δ' i} {cs : ∀ i → prod Γ (δ i) ⇒ δ'' i}
      {x : prod Γ Y ⇒ Z} {y : prod Γ X ⇒ Y} {z : prod Γ X ⇒ Z} →
      (∀ i → (as i ∘co bs i) ≈ cs i) → ((x ∘co y) ≈ z) →
      ∀ i → (strong-extend-mor as x i ∘co strong-extend-mor bs y i) ≈ strong-extend-mor cs z i
    strong-extend-mor-comp es ez Fin.zero    = ez
    strong-extend-mor-comp es ez (Fin.suc i) = es i

    mutual
      strong-fmor-comp : ∀ {k} {Γ : obj} (P : Poly 𝒞 k) {δ δ' δ'' : Fin k → obj}
                         (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                         (strong-fmor P gs ∘co strong-fmor P fs) ≈ strong-fmor P (λ i → gs i ∘co fs i)
      strong-fmor-comp (const A) gs fs = CoK.id-left
      strong-fmor-comp (var i)   gs fs = ≈-refl
      strong-fmor-comp (P + Q)   gs fs =
        ≈-trans (copair-comp _ _ _ _)
                (copair-cong (∘-cong ≈-refl (≈-trans (under-co _ _) (under-cong (strong-fmor-comp P gs fs))))
                             (∘-cong ≈-refl (≈-trans (under-co _ _) (under-cong (strong-fmor-comp Q gs fs)))))
      strong-fmor-comp (P × Q)   gs fs =
        ≈-trans (under-co _ _)
                (under-cong (≈-trans (strong-prod-m-comp _ _ _ _)
                                     (strong-prod-m-cong (strong-fmor-comp P gs fs) (strong-fmor-comp Q gs fs))))
      strong-fmor-comp (μ P)     gs fs = strong-μ-fmor-comp P gs fs

      -- Fusion: postcomposition with an algebra morphism takes folds to folds.
      fusion : ∀ {k} {Γ A B : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj}
               (a : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A)
               (b : prod Γ (fobj μ-obj P (extend δ B)) ⇒ B)
               (h : prod Γ A ⇒ B) →
               ((h ∘co a) ≈ (b ∘co strong-fmor P (strong-extend-mor (λ i → p₂) h))) →
               (h ∘co ⦅ a ⦆) ≈ ⦅ b ⦆
      fusion {P = P} {δ = δ} a b h hyp =
        ⦅⦆-η b (h ∘co ⦅ a ⦆)
          (begin
            (h ∘co ⦅ a ⦆) ∘co (inMap P δ ∘ p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            h ∘co (⦅ a ⦆ ∘co (inMap P δ ∘ p₂))
          ≈⟨ CoK.∘-cong ≈-refl (⦅⦆-β {P = P} {δ = δ} a) ⟩
            h ∘co (a ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) ⦅ a ⦆))
          ≈˘⟨ CoK.assoc _ _ _ ⟩
            (h ∘co a) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) ⦅ a ⦆)
          ≈⟨ CoK.∘-cong hyp ≈-refl ⟩
            (b ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) h)) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) ⦅ a ⦆)
          ≈⟨ CoK.assoc _ _ _ ⟩
            b ∘co (strong-fmor P (strong-extend-mor (λ _ → p₂) h) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) ⦅ a ⦆))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
                                        (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-left) ≈-refl))) ⟩
            b ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (h ∘co ⦅ a ⦆))
          ∎)
        where open ≈-Reasoning isEquiv

      strong-μ-fmor-comp : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) {δ δ' δ'' : Fin k → obj}
                           (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                           (strong-μ-fmor P gs ∘co strong-μ-fmor P fs) ≈ strong-μ-fmor P (λ i → gs i ∘co fs i)
      strong-μ-fmor-comp P {δ} {δ'} {δ''} gs fs =
        fusion alg-f alg μ-gs head'
        where
          μ-gs = strong-μ-fmor P gs
          alg-f = inMap P δ' ∘ strong-fmor P (strong-extend-mor fs p₂)
          alg-g = inMap P δ'' ∘ strong-fmor P (strong-extend-mor gs p₂)
          alg = inMap P δ'' ∘ strong-fmor P (strong-extend-mor (λ i → gs i ∘co fs i) p₂)

          head : (μ-gs ∘co alg-f) ≈ (alg-g ∘co strong-fmor P (strong-extend-mor fs μ-gs))
          head =
            begin
              μ-gs ∘co (inMap P δ' ∘ strong-fmor P (strong-extend-mor fs p₂))
            ≈˘⟨ ∘co-push μ-gs (inMap P δ') _ ⟩
              (μ-gs ∘co (inMap P δ' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor fs p₂)
            ≈⟨ CoK.∘-cong (⦅⦆-β {P = P} {δ = δ'} alg-g) ≈-refl ⟩
              (alg-g ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs)) ∘co strong-fmor P (strong-extend-mor fs p₂)
            ≈⟨ CoK.assoc _ _ _ ⟩
              alg-g ∘co (strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs) ∘co strong-fmor P (strong-extend-mor fs p₂))
            ≈⟨ CoK.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
                                          (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-left) CoK.id-right))) ⟩
              alg-g ∘co strong-fmor P (strong-extend-mor fs μ-gs)
            ∎ where open ≈-Reasoning isEquiv

          head' : (μ-gs ∘co alg-f) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs))
          head' =
            begin
              μ-gs ∘co alg-f
            ≈⟨ head ⟩
              alg-g ∘co strong-fmor P (strong-extend-mor fs μ-gs)
            ≈⟨ assoc _ _ _ ⟩
              inMap P δ'' ∘ (strong-fmor P (strong-extend-mor gs p₂) ∘co strong-fmor P (strong-extend-mor fs μ-gs))
            ≈⟨ ∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
                                      (strong-fmor-cong P (strong-extend-mor-comp (λ _ → ≈-refl) CoK.id-left))) ⟩
              inMap P δ'' ∘ strong-fmor P (strong-extend-mor (λ j → gs j ∘co fs j) μ-gs)
            ≈˘⟨ ∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
                                       (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-right) CoK.id-left))) ⟩
              inMap P δ'' ∘ (strong-fmor P (strong-extend-mor (λ j → gs j ∘co fs j) p₂) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs))
            ≈˘⟨ assoc _ _ _ ⟩
              alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs)
            ∎ where open ≈-Reasoning isEquiv

    -- The strong action at the projections is the projection.
    mutual
      strong-fmor-p₂ : ∀ {k} {Γ : obj} (P : Poly 𝒞 k) {δ : Fin k → obj} →
                       strong-fmor {Γ = Γ} P {δ} {δ} (λ i → p₂) ≈ p₂
      strong-fmor-p₂ (const A) = ≈-refl
      strong-fmor-p₂ (var i)   = ≈-refl
      strong-fmor-p₂ (P + Q)   =
        ≈-trans (copair-cong (∘-cong ≈-refl (≈-trans (under-cong (strong-fmor-p₂ P)) under-p₂))
                             (∘-cong ≈-refl (≈-trans (under-cong (strong-fmor-p₂ Q)) under-p₂)))
                copair-ext0
      strong-fmor-p₂ (P × Q)   =
        ≈-trans (under-cong (≈-trans (strong-prod-m-cong (strong-fmor-p₂ P) (strong-fmor-p₂ Q))
                                     (≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _)) (pair-ext _))))
                under-p₂
      strong-fmor-p₂ (μ P)     = strong-μ-fmor-p₂ P

      strong-μ-fmor-p₂ : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) {δ : Fin k → obj} →
                         strong-μ-fmor {Γ = Γ} P {δ} {δ} (λ i → p₂) ≈ p₂
      strong-μ-fmor-p₂ P {δ} =
        ≈-sym (⦅⦆-η {P = P} {δ = δ} alg₀ p₂ premise)
        where
          alg₀ : prod _ (fobj μ-obj P (extend δ (μ-obj P δ))) ⇒ μ-obj P δ
          alg₀ = inMap P δ ∘ strong-fmor P (strong-extend-mor {X = μ-obj P δ} {Y = μ-obj P δ} (λ _ → p₂) p₂)

          es₀ : ∀ i → strong-extend-mor {X = μ-obj P δ} {Y = μ-obj P δ} (λ _ → p₂) p₂ i ≈ p₂
          es₀ Fin.zero    = ≈-refl
          es₀ (Fin.suc i) = ≈-refl

          rhs : (alg₀ ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) p₂)) ≈ (inMap P δ ∘ p₂)
          rhs =
            begin
              alg₀ ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) p₂)
            ≈⟨ assoc _ _ _ ⟩
              inMap P δ ∘ (strong-fmor P (strong-extend-mor (λ _ → p₂) p₂) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) p₂))
            ≈⟨ ∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
                                      (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-left) CoK.id-left))) ⟩
              inMap P δ ∘ strong-fmor P (strong-extend-mor (λ _ → p₂) p₂)
            ≈⟨ ∘-cong ≈-refl (strong-fmor-cong P es₀) ⟩
              inMap P δ ∘ strong-fmor P (λ i → p₂)
            ≈⟨ ∘-cong ≈-refl (strong-fmor-p₂ P) ⟩
              inMap P δ ∘ p₂
            ∎ where open ≈-Reasoning isEquiv

          premise : (p₂ ∘co (inMap P δ ∘ p₂)) ≈ (alg₀ ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) p₂))
          premise = ≈-trans CoK.id-left (≈-sym rhs)

    -- Reflection: the fold of the algebra map is the identity.
    ⦅⦆-reflect : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) (δ : Fin k → obj) →
                 ⦅_⦆ {Γ = Γ} {P = P} {δ = δ} (inMap P δ ∘ p₂) ≈ p₂
    ⦅⦆-reflect P δ =
      ≈-sym (⦅⦆-η {P = P} {δ = δ} (inMap P δ ∘ p₂) p₂
        (≈-trans CoK.id-left
          (≈-sym (≈-trans (assoc _ _ _)
                          (∘-cong ≈-refl (≈-trans (pair-p₂ _ _)
                                                  (≈-trans (strong-fmor-cong P es₀) (strong-fmor-p₂ P))))))))
      where
        es₀ : ∀ i → strong-extend-mor {X = μ-obj P δ} {Y = μ-obj P δ} (λ _ → p₂) p₂ i ≈ p₂
        es₀ Fin.zero    = ≈-refl
        es₀ (Fin.suc i) = ≈-refl

-- Action of a functor on polynomials: apply the functor at the const leaves.
Poly-map : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} →
           Functor 𝒞 𝒟 → ∀ {n} → Poly 𝒞 n → Poly 𝒟 n
Poly-map F (const A) = const (F .Functor.fobj A)
Poly-map F (var i)   = var i
Poly-map F (P + Q)   = Poly-map F P + Poly-map F Q
Poly-map F (P × Q)   = Poly-map F P × Poly-map F Q
Poly-map F (μ P)     = μ (Poly-map F P)

