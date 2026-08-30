{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Level using (_⊔_)
open import categories using (Category; HasProducts; HasCoproducts; HasStrongCoproducts; HasTerminal; coKleisli-prod;
                              strong-coproducts→coproducts; module Unitor)
open import prop-setoid using (module ≈-Reasoning)
open import functor using (Functor; StrongFunctor)

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

-- Interpretation of the polynomials with a strong endofunctor L applied at every sum and product;
-- initial algebras for the μ-polynomials, with the catamorphism in context, and the laws of the fold.
module Interp
  {o m e} {𝒞 : Category o m e} (𝒞P : HasProducts 𝒞) (𝒞SC : HasStrongCoproducts 𝒞 𝒞P)
  (𝒞L : StrongFunctor 𝒞P)
  where

  open Category 𝒞
  open HasProducts 𝒞P
  open HasStrongCoproducts 𝒞SC
  open StrongFunctor 𝒞L using (strengthᵣ; strengthᵣ-natural; strengthᵣ-p₂; strengthᵣ-assoc)
    renaming (fobj to L; fmor to Lmap; fmor-cong to Lmap-cong; fmor-id to Lmap-id; fmor-comp to Lmap-comp)

  strong-Lmap : ∀ {Γ X Y} → prod Γ X ⇒ Y → prod Γ (L X) ⇒ L Y
  strong-Lmap f = Lmap f ∘ strengthᵣ

  strong-Lmap-cong : ∀ {Γ X Y} {f g : prod Γ X ⇒ Y} → f ≈ g → strong-Lmap f ≈ strong-Lmap g
  strong-Lmap-cong e = ∘-cong (Lmap-cong e) ≈-refl

  strong-Lmap-comp : ∀ {Γ X Y Z} (f : prod Γ Y ⇒ Z) (g : prod Γ X ⇒ Y) →
                     (strong-Lmap f ∘ pair p₁ (strong-Lmap g)) ≈ strong-Lmap (f ∘ pair p₁ g)
  strong-Lmap-comp f g =
    begin
      (Lmap f ∘ strengthᵣ) ∘ pair p₁ (Lmap g ∘ strengthᵣ)
    ≈⟨ assoc _ _ _ ⟩
      Lmap f ∘ (strengthᵣ ∘ pair p₁ (Lmap g ∘ strengthᵣ))
    ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (≈-trans (pair-compose _ _ _ _) (pair-cong id-left ≈-refl))) ⟩
      Lmap f ∘ (strengthᵣ ∘ (prod-m (id _) (Lmap g) ∘ pair p₁ strengthᵣ))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      Lmap f ∘ ((strengthᵣ ∘ prod-m (id _) (Lmap g)) ∘ pair p₁ strengthᵣ)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (strengthᵣ-natural (id _) g) ≈-refl) ⟩
      Lmap f ∘ ((Lmap (prod-m (id _) g) ∘ strengthᵣ) ∘ pair p₁ strengthᵣ)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      Lmap f ∘ (Lmap (prod-m (id _) g) ∘ (strengthᵣ ∘ pair p₁ strengthᵣ))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl strengthᵣ-assoc) ⟩
      Lmap f ∘ (Lmap (prod-m (id _) g) ∘ (Lmap (pair p₁ (id _)) ∘ strengthᵣ))
    ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      Lmap f ∘ ((Lmap (prod-m (id _) g) ∘ Lmap (pair p₁ (id _))) ∘ strengthᵣ)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (Lmap-comp _ _) ≈-refl) ⟩
      Lmap f ∘ (Lmap (prod-m (id _) g ∘ pair p₁ (id _)) ∘ strengthᵣ)
    ≈⟨ ∘-cong ≈-refl (∘-cong (Lmap-cong (≈-trans (pair-compose _ _ _ _) (pair-cong id-left id-right))) ≈-refl) ⟩
      Lmap f ∘ (Lmap (pair p₁ g) ∘ strengthᵣ)
    ≈˘⟨ assoc _ _ _ ⟩
      (Lmap f ∘ Lmap (pair p₁ g)) ∘ strengthᵣ
    ≈˘⟨ ∘-cong (Lmap-comp _ _) ≈-refl ⟩
      Lmap (f ∘ pair p₁ g) ∘ strengthᵣ
    ∎ where open ≈-Reasoning isEquiv

  strong-Lmap-p₂ : ∀ {Γ X} → strong-Lmap (p₂ {Γ} {X}) ≈ p₂
  strong-Lmap-p₂ = strengthᵣ-p₂

  strong-Lmap-pre : ∀ {Γ Γ' X X' Y} (u : Γ ⇒ Γ') (f : prod Γ' X' ⇒ Y) (c : X ⇒ X') →
                    (strong-Lmap f ∘ prod-m u (Lmap c)) ≈ strong-Lmap (f ∘ prod-m u c)
  strong-Lmap-pre u f c =
    begin
      (Lmap f ∘ strengthᵣ) ∘ prod-m u (Lmap c)
    ≈⟨ assoc _ _ _ ⟩
      Lmap f ∘ (strengthᵣ ∘ prod-m u (Lmap c))
    ≈˘⟨ ∘-cong ≈-refl (strengthᵣ-natural u c) ⟩
      Lmap f ∘ (Lmap (prod-m u c) ∘ strengthᵣ)
    ≈˘⟨ assoc _ _ _ ⟩
      (Lmap f ∘ Lmap (prod-m u c)) ∘ strengthᵣ
    ≈˘⟨ ∘-cong (Lmap-comp _ _) ≈-refl ⟩
      Lmap (f ∘ prod-m u c) ∘ strengthᵣ
    ∎ where open ≈-Reasoning isEquiv

  strong-Lmap-reindex : ∀ {Γ Γ' X Y} (u : Γ ⇒ Γ') (f : prod Γ' X ⇒ Y) →
                        (strong-Lmap f ∘ prod-m u (id _)) ≈ strong-Lmap (f ∘ prod-m u (id _))
  strong-Lmap-reindex u f =
    ≈-trans (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym Lmap-id))) (strong-Lmap-pre u f (id _))

  strong-Lmap-post : ∀ {Γ X Y Z} (h : Y ⇒ Z) (f : prod Γ X ⇒ Y) →
                     (Lmap h ∘ strong-Lmap f) ≈ strong-Lmap (h ∘ f)
  strong-Lmap-post h f = head-cong (≈-sym (Lmap-comp _ _))

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
      strong-fmor (P + Q)   fs = copair (in₁ ∘ strong-Lmap (strong-fmor P fs)) (in₂ ∘ strong-Lmap (strong-fmor Q fs))
      strong-fmor (P × Q)   fs = strong-Lmap (strong-prod-m (strong-fmor P fs) (strong-fmor Q fs))
      strong-fmor (μ P)     fs = strong-μ-fmor P fs

      strong-μ-fmor : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) {δ δ' : Fin k → obj} →
                      (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
      strong-μ-fmor P {δ} {δ'} fs = ⦅ inMap P δ' ∘ strong-fmor P (strong-extend-mor fs p₂) ⦆

    module WithTerminal (𝒞T : HasTerminal 𝒞) where
      open HasTerminal 𝒞T using (to-terminal)

      fmor : ∀ {k} (P : Poly 𝒞 k) {δ δ' : Fin k → obj} → (∀ i → δ i ⇒ δ' i) → fobj μ-obj P δ ⇒ fobj μ-obj P δ'
      fmor P fs = strong-fmor P (λ i → fs i ∘ p₂) ∘ pair to-terminal (id _)

      μ-map : ∀ {j k} (P : Poly 𝒞 (suc j)) (δ : Fin j → obj) (Q : Poly 𝒞 (suc k)) (δ' : Fin k → obj) →
              fobj μ-obj P (extend δ (μ-obj Q δ')) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ')) →
              μ-obj P δ ⇒ μ-obj Q δ'
      μ-map P δ Q δ' u = ⦅_⦆ {P = P} {δ = δ} ((inMap Q δ' ∘ u) ∘ p₂) ∘ pair to-terminal (id _)

  extend-mor : ∀ {k} {δ δ' : Fin k → obj} {X Y : obj} → (∀ i → δ i ⇒ δ' i) → X ⇒ Y →
               ∀ i → extend δ X i ⇒ extend δ' Y i
  extend-mor fs xy Fin.zero    = xy
  extend-mor fs xy (Fin.suc i) = fs i

  infixl 21 _∘co_
  _∘co_ : ∀ {Γ X Y Z} → prod Γ Y ⇒ Z → prod Γ X ⇒ Y → prod Γ X ⇒ Z
  f ∘co g = f ∘ pair p₁ g

  record HasMuLaws (Mu : HasMu) : Set (o ⊔ m ⊔ e) where
    open HasMu Mu hiding (module WithTerminal)
    field
      ⦅⦆-β : ∀ {k} {Γ A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) →
             (⦅ alg ⦆ ∘co (inMap P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) ⦅ alg ⦆))
      ⦅⦆-η : ∀ {k} {Γ A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) (h : prod Γ (μ-obj P δ) ⇒ A) →
             (h ∘co (inMap P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) h)) → h ≈ ⦅ alg ⦆

    private module coKl {Γ : obj} = Category (coKleisli-prod 𝒞P Γ)

    ⦅⦆-cong : ∀ {k} {Γ A : obj} (P : Poly 𝒞 (suc k)) (δ : Fin k → obj)
              {alg alg' : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A} →
              alg ≈ alg' → ⦅_⦆ {P = P} {δ = δ} alg ≈ ⦅_⦆ {P = P} {δ = δ} alg'
    ⦅⦆-cong P δ {alg} {alg'} e =
      ⦅⦆-η {P = P} {δ = δ} alg' (⦅_⦆ {P = P} {δ = δ} alg)
        (≈-trans (⦅⦆-β {P = P} {δ = δ} alg) (∘-cong e ≈-refl))

    ∘co-push : ∀ {Γ W X Y Z} (x : prod Γ Y ⇒ Z) (a : X ⇒ Y) (y : prod Γ W ⇒ X) →
               ((x ∘co (a ∘ p₂)) ∘co y) ≈ (x ∘co (a ∘ y))
    ∘co-push x a y =
      begin
        (x ∘ pair p₁ (a ∘ p₂)) ∘ pair p₁ y
      ≈⟨ coKl.assoc _ _ _ ⟩
        x ∘ pair p₁ ((a ∘ p₂) ∘ pair p₁ y)
      ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (tail-cong (pair-p₂ _ _))) ⟩
        x ∘ pair p₁ (a ∘ y)
      ∎ where open ≈-Reasoning isEquiv

    copair-comp : ∀ {Γ X₁ X₂ Y₁ Y₂ Z₁ Z₂}
      (f₂ : prod Γ Y₁ ⇒ Z₁) (g₂ : prod Γ Y₂ ⇒ Z₂) (f₁ : prod Γ X₁ ⇒ Y₁) (g₁ : prod Γ X₂ ⇒ Y₂) →
      (copair (in₁ ∘ f₂) (in₂ ∘ g₂) ∘co copair (in₁ ∘ f₁) (in₂ ∘ g₁))
        ≈ copair (in₁ ∘ (f₂ ∘co f₁)) (in₂ ∘ (g₂ ∘co g₁))
    copair-comp f₂ g₂ f₁ g₁ =
      ≈-trans (≈-sym (copair-ext _)) (copair-cong (branch (copair-in₁ _ _) (copair-in₁ _ _)) (branch (copair-in₂ _ _) (copair-in₂ _ _)))
      where
        G = copair (in₁ ∘ f₂) (in₂ ∘ g₂)
        F = copair (in₁ ∘ f₁) (in₂ ∘ g₁)

        branch : ∀ {A C E} {ι : A ⇒ _} {ι' : C ⇒ _} {ι'' : E ⇒ _} {h₁ : prod _ A ⇒ C} {h₂ : prod _ C ⇒ E} →
                 (F ∘co (ι ∘ p₂)) ≈ (ι' ∘ h₁) → (G ∘co (ι' ∘ p₂)) ≈ (ι'' ∘ h₂) →
                 ((G ∘co F) ∘co (ι ∘ p₂)) ≈ (ι'' ∘ (h₂ ∘co h₁))
        branch {ι' = ι'} {h₁ = h₁} e₁ e₂ =
          ≈-trans (coKl.assoc _ _ _)
          (≈-trans (coKl.∘-cong ≈-refl e₁)
          (≈-trans (≈-sym (∘co-push G ι' h₁)) (≈-trans (coKl.∘-cong e₂ ≈-refl) (assoc _ _ _))))

    mutual
      strong-fmor-cong : ∀ {k} {Γ : obj} (P : Poly 𝒞 k) {δ δ' : Fin k → obj}
                         {fs fs' : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                         (∀ i → fs i ≈ fs' i) → strong-fmor P fs ≈ strong-fmor P fs'
      strong-fmor-cong (const A) es = ≈-refl
      strong-fmor-cong (var i)   es = es i
      strong-fmor-cong (P + Q)   es =
        copair-cong (∘-cong ≈-refl (strong-Lmap-cong (strong-fmor-cong P es)))
                    (∘-cong ≈-refl (strong-Lmap-cong (strong-fmor-cong Q es)))
      strong-fmor-cong (P × Q)   es =
        strong-Lmap-cong (strong-prod-m-cong (strong-fmor-cong P es) (strong-fmor-cong Q es))
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
      strong-fmor-comp (const A) gs fs = coKl.id-left
      strong-fmor-comp (var i)   gs fs = ≈-refl
      strong-fmor-comp (P + Q)   gs fs =
        ≈-trans (copair-comp _ _ _ _)
                (copair-cong (∘-cong ≈-refl (≈-trans (strong-Lmap-comp _ _) (strong-Lmap-cong (strong-fmor-comp P gs fs))))
                             (∘-cong ≈-refl (≈-trans (strong-Lmap-comp _ _) (strong-Lmap-cong (strong-fmor-comp Q gs fs)))))
      strong-fmor-comp (P × Q)   gs fs =
        ≈-trans (strong-Lmap-comp _ _)
                (strong-Lmap-cong (≈-trans (strong-prod-m-comp _ _ _ _)
                                     (strong-prod-m-cong (strong-fmor-comp P gs fs) (strong-fmor-comp Q gs fs))))
      strong-fmor-comp (μ P)     gs fs = strong-μ-fmor-comp P gs fs

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
          ≈⟨ coKl.assoc _ _ _ ⟩
            h ∘co (⦅ a ⦆ ∘co (inMap P δ ∘ p₂))
          ≈⟨ coKl.∘-cong ≈-refl (⦅⦆-β {P = P} {δ = δ} a) ⟩
            h ∘co (a ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) ⦅ a ⦆))
          ≈˘⟨ coKl.assoc _ _ _ ⟩
            (h ∘co a) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) ⦅ a ⦆)
          ≈⟨ coKl.∘-cong hyp ≈-refl ⟩
            (b ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) h)) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) ⦅ a ⦆)
          ≈⟨ coKl.assoc _ _ _ ⟩
            b ∘co (strong-fmor P (strong-extend-mor (λ _ → p₂) h) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) ⦅ a ⦆))
          ≈⟨ coKl.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
                                        (strong-fmor-cong P (strong-extend-mor-comp (λ _ → coKl.id-left) ≈-refl))) ⟩
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
            ≈⟨ coKl.∘-cong (⦅⦆-β {P = P} {δ = δ'} alg-g) ≈-refl ⟩
              (alg-g ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs)) ∘co strong-fmor P (strong-extend-mor fs p₂)
            ≈⟨ coKl.assoc _ _ _ ⟩
              alg-g ∘co (strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs) ∘co strong-fmor P (strong-extend-mor fs p₂))
            ≈⟨ coKl.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
                                          (strong-fmor-cong P (strong-extend-mor-comp (λ _ → coKl.id-left) coKl.id-right))) ⟩
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
                                      (strong-fmor-cong P (strong-extend-mor-comp (λ _ → ≈-refl) coKl.id-left))) ⟩
              inMap P δ'' ∘ strong-fmor P (strong-extend-mor (λ j → gs j ∘co fs j) μ-gs)
            ≈˘⟨ ∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _)
                                       (strong-fmor-cong P (strong-extend-mor-comp (λ _ → coKl.id-right) coKl.id-left))) ⟩
              inMap P δ'' ∘ (strong-fmor P (strong-extend-mor (λ j → gs j ∘co fs j) p₂) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs))
            ≈˘⟨ assoc _ _ _ ⟩
              alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs)
            ∎ where open ≈-Reasoning isEquiv

    fusion-inMap : ∀ {j k} {Γ A : obj} (P : Poly 𝒞 (suc j)) (δ : Fin j → obj) (Q : Poly 𝒞 (suc k)) (δ' : Fin k → obj)
                   (alg : prod Γ (fobj μ-obj Q (extend δ' A)) ⇒ A)
                   (b : prod Γ (fobj μ-obj P (extend δ (μ-obj Q δ'))) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ')))
                   (b' : prod Γ (fobj μ-obj P (extend δ A)) ⇒ fobj μ-obj Q (extend δ' A)) →
                   ((strong-fmor Q (strong-extend-mor (λ i → p₂) (⦅_⦆ {P = Q} {δ = δ'} alg)) ∘co b)
                      ≈ (b' ∘co strong-fmor P (strong-extend-mor (λ i → p₂) (⦅_⦆ {P = Q} {δ = δ'} alg)))) →
                   (⦅_⦆ {P = Q} {δ = δ'} alg ∘co ⦅_⦆ {P = P} {δ = δ} (inMap Q δ' ∘ b)) ≈ ⦅_⦆ {P = P} {δ = δ} (alg ∘co b')
    fusion-inMap P δ Q δ' alg b b' sq =
      fusion {P = P} {δ = δ} (inMap Q δ' ∘ b) (alg ∘co b') (⦅_⦆ {P = Q} {δ = δ'} alg)
        (≈-trans (≈-sym (∘co-push _ (inMap Q δ') b))
        (≈-trans (coKl.∘-cong (⦅⦆-β {P = Q} {δ = δ'} alg) ≈-refl)
        (≈-trans (coKl.assoc _ _ _)
        (≈-trans (coKl.∘-cong ≈-refl sq) (≈-sym (coKl.assoc _ _ _))))))

    mutual
      strong-fmor-p₂ : ∀ {k} {Γ : obj} (P : Poly 𝒞 k) {δ : Fin k → obj} →
                       strong-fmor {Γ = Γ} P {δ} {δ} (λ i → p₂) ≈ p₂
      strong-fmor-p₂ (const A) = ≈-refl
      strong-fmor-p₂ (var i)   = ≈-refl
      strong-fmor-p₂ (P + Q)   =
        ≈-trans (copair-cong (∘-cong ≈-refl (≈-trans (strong-Lmap-cong (strong-fmor-p₂ P)) strong-Lmap-p₂))
                             (∘-cong ≈-refl (≈-trans (strong-Lmap-cong (strong-fmor-p₂ Q)) strong-Lmap-p₂)))
                copair-ext0
      strong-fmor-p₂ (P × Q)   =
        ≈-trans (strong-Lmap-cong (≈-trans (strong-prod-m-cong (strong-fmor-p₂ P) (strong-fmor-p₂ Q))
                                     (≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _)) (pair-ext _))))
                strong-Lmap-p₂
      strong-fmor-p₂ (μ P)     = strong-μ-fmor-p₂ P

      strong-fmor-ext-p₂ : ∀ {k} {Γ X : obj} (P : Poly 𝒞 (suc k)) {δ : Fin k → obj} →
                           strong-fmor {Γ = Γ} P (strong-extend-mor {δ = δ} {δ' = δ} {X = X} {Y = X} (λ i → p₂) p₂) ≈ p₂
      strong-fmor-ext-p₂ {X = X} P = ≈-trans (strong-fmor-cong P es) (strong-fmor-p₂ P)
        where
          es : ∀ i → strong-extend-mor {X = X} {Y = X} (λ _ → p₂) p₂ i ≈ p₂
          es Fin.zero    = ≈-refl
          es (Fin.suc i) = ≈-refl

      strong-μ-fmor-p₂ : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) {δ : Fin k → obj} →
                         strong-μ-fmor {Γ = Γ} P {δ} {δ} (λ i → p₂) ≈ p₂
      strong-μ-fmor-p₂ P {δ} = ≈-trans (⦅⦆-cong P δ (∘-cong ≈-refl (strong-fmor-ext-p₂ P))) (⦅⦆-reflect P δ)

      ⦅⦆-reflect : ∀ {k} {Γ : obj} (P : Poly 𝒞 (suc k)) (δ : Fin k → obj) →
                   ⦅_⦆ {Γ = Γ} {P = P} {δ = δ} (inMap P δ ∘ p₂) ≈ p₂
      ⦅⦆-reflect P δ =
        ≈-sym (⦅⦆-η {P = P} {δ = δ} (inMap P δ ∘ p₂) p₂
          (≈-trans coKl.id-left
            (≈-sym (tail-cong (≈-trans (pair-p₂ _ _)
                                       (strong-fmor-ext-p₂ P))))))

    mutual
      strong-fmor-reindex : ∀ {k} {Γ Γ' : obj} (P : Poly 𝒞 k) {δ δ' : Fin k → obj}
                            (u : Γ ⇒ Γ') (fs : ∀ i → prod Γ' (δ i) ⇒ δ' i) →
                            (strong-fmor P fs ∘ prod-m u (id _)) ≈ strong-fmor P (λ i → fs i ∘ prod-m u (id _))
      strong-fmor-reindex (const A) u fs = ≈-trans (pair-p₂ _ _) id-left
      strong-fmor-reindex (var i)   u fs = ≈-refl
      strong-fmor-reindex (P + Q)   u fs =
        ≈-trans (copair-reindex u _ _)
                (copair-cong
                  (tail-cong (≈-trans (strong-Lmap-reindex u _)
                                      (strong-Lmap-cong (strong-fmor-reindex P u fs))))
                  (tail-cong (≈-trans (strong-Lmap-reindex u _)
                                      (strong-Lmap-cong (strong-fmor-reindex Q u fs)))))
      strong-fmor-reindex (P × Q)   u fs =
        ≈-trans (strong-Lmap-reindex u _)
                (strong-Lmap-cong
                  (≈-trans (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym prod-m-id)))
                    (≈-trans (strong-prod-m-pre _ _ u (id _) (id _))
                      (strong-prod-m-cong (strong-fmor-reindex P u fs) (strong-fmor-reindex Q u fs)))))
      strong-fmor-reindex (μ P)     u fs = strong-μ-fmor-reindex P u fs

      strong-μ-fmor-reindex : ∀ {k} {Γ Γ' : obj} (P : Poly 𝒞 (suc k)) {δ δ' : Fin k → obj}
                              (u : Γ ⇒ Γ') (fs : ∀ i → prod Γ' (δ i) ⇒ δ' i) →
                              (strong-μ-fmor P fs ∘ prod-m u (id _)) ≈ strong-μ-fmor P (λ i → fs i ∘ prod-m u (id _))
      strong-μ-fmor-reindex P {δ} {δ'} u fs =
        ≈-trans (⦅⦆-reindex u (inMap P δ' ∘ strong-fmor P (strong-extend-mor fs p₂)))
                (⦅⦆-cong P δ
                  (tail-cong (≈-trans (strong-fmor-reindex P u (strong-extend-mor fs p₂))
                                      (strong-fmor-cong P es))))
        where
        es : ∀ i → (strong-extend-mor fs p₂ i ∘ prod-m u (id _))
                     ≈ strong-extend-mor (λ j → fs j ∘ prod-m u (id _)) p₂ i
        es Fin.zero    = ≈-trans (pair-p₂ _ _) id-left
        es (Fin.suc i) = ≈-refl

      ⦅⦆-reindex : ∀ {k} {Γ Γ' A : obj} {P : Poly 𝒞 (suc k)} {δ : Fin k → obj} (u : Γ ⇒ Γ')
                   (alg : prod Γ' (fobj μ-obj P (extend δ A)) ⇒ A) →
                   (⦅ alg ⦆ ∘ prod-m u (id _)) ≈ ⦅ alg ∘ prod-m u (id _) ⦆
      ⦅⦆-reindex {Γ = Γ} {Γ'} {A} {P = P} {δ} u alg =
        ⦅⦆-η {P = P} {δ = δ} (alg ∘ prod-m u (id _)) (⦅ alg ⦆ ∘ prod-m u (id _)) premise
        where
        SF : prod Γ' (fobj μ-obj P (extend δ (μ-obj P δ))) ⇒ fobj μ-obj P (extend δ A)
        SF = strong-fmor P (strong-extend-mor (λ i → p₂) ⦅ alg ⦆)

        SF' : prod Γ (fobj μ-obj P (extend δ (μ-obj P δ))) ⇒ fobj μ-obj P (extend δ A)
        SF' = strong-fmor P (strong-extend-mor (λ i → p₂) (⦅ alg ⦆ ∘ prod-m u (id _)))

        es : ∀ i → (strong-extend-mor (λ j → p₂) ⦅ alg ⦆ i ∘ prod-m u (id _))
                     ≈ strong-extend-mor (λ j → p₂) (⦅ alg ⦆ ∘ prod-m u (id _)) i
        es Fin.zero    = ≈-refl
        es (Fin.suc i) = ≈-trans (pair-p₂ _ _) id-left

        step : (pair p₁ SF ∘ prod-m u (id _)) ≈ (prod-m u (id _) ∘ pair p₁ SF')
        step =
          ≈-trans (pair-natural _ _ _)
          (≈-trans (pair-cong (pair-p₁ _ _)
                     (≈-trans (strong-fmor-reindex P u (strong-extend-mor (λ i → p₂) ⦅ alg ⦆))
                              (strong-fmor-cong P es)))
            (≈-sym (≈-trans (pair-compose _ _ _ _) (pair-cong ≈-refl id-left))))

        premise : ((⦅ alg ⦆ ∘ prod-m u (id _)) ∘co (inMap P δ ∘ p₂)) ≈ ((alg ∘ prod-m u (id _)) ∘co SF')
        premise = begin
            (⦅ alg ⦆ ∘ prod-m u (id _)) ∘ pair p₁ (inMap P δ ∘ p₂)
          ≈⟨ assoc _ _ _ ⟩
            ⦅ alg ⦆ ∘ (prod-m u (id _) ∘ pair p₁ (inMap P δ ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (prodm-pair-interchange u (inMap P δ)) ⟩
            ⦅ alg ⦆ ∘ (pair p₁ (inMap P δ ∘ p₂) ∘ prod-m u (id _))
          ≈˘⟨ assoc _ _ _ ⟩
            (⦅ alg ⦆ ∘co (inMap P δ ∘ p₂)) ∘ prod-m u (id _)
          ≈⟨ ∘-cong (⦅⦆-β {P = P} {δ = δ} alg) ≈-refl ⟩
            (alg ∘co SF) ∘ prod-m u (id _)
          ≈⟨ assoc _ _ _ ⟩
            alg ∘ (pair p₁ SF ∘ prod-m u (id _))
          ≈⟨ ∘-cong ≈-refl step ⟩
            alg ∘ (prod-m u (id _) ∘ pair p₁ SF')
          ≈˘⟨ assoc _ _ _ ⟩
            (alg ∘ prod-m u (id _)) ∘ pair p₁ SF'
          ∎ where open ≈-Reasoning isEquiv

    module WithTerminal (𝒞T : HasTerminal 𝒞) where
      open HasTerminal 𝒞T using (to-terminal; to-terminal-unique)
      open Unitor 𝒞T 𝒞P using (sect; sect-pre; sect-natural; unitor-comp)
      open HasMu.WithTerminal Mu 𝒞T

      fmor-cong : ∀ {k} (P : Poly 𝒞 k) {δ δ' : Fin k → obj} {fs gs : ∀ i → δ i ⇒ δ' i} →
                  (∀ i → fs i ≈ gs i) → fmor P fs ≈ fmor P gs
      fmor-cong P es = ∘-cong (strong-fmor-cong P (λ i → ∘-cong (es i) ≈-refl)) ≈-refl

      fmor-id : ∀ {k} (P : Poly 𝒞 k) {δ : Fin k → obj} → fmor P (λ i → id (δ i)) ≈ id _
      fmor-id P =
        ≈-trans (∘-cong (≈-trans (strong-fmor-cong P (λ i → id-left)) (strong-fmor-p₂ P)) ≈-refl)
                (pair-p₂ _ _)

      fmor-comp : ∀ {k} (P : Poly 𝒞 k) {δ δ' δ'' : Fin k → obj}
                  (gs : ∀ i → δ' i ⇒ δ'' i) (fs : ∀ i → δ i ⇒ δ' i) →
                  (fmor P gs ∘ fmor P fs) ≈ fmor P (λ i → gs i ∘ fs i)
      fmor-comp P gs fs =
        ≈-trans (unitor-comp _ _)
                (∘-cong (≈-trans (strong-fmor-comp P _ _)
                                 (strong-fmor-cong P (λ i → tail-cong-assoc (pair-p₂ _ _))))
                        ≈-refl)

      private
        𝟙 = HasTerminal.witness 𝒞T

        sect-p₂-id : ∀ {X} → (sect ∘ p₂ {𝟙} {X}) ≈ id _
        sect-p₂-id = ≈-trans (sect-pre _) (≈-trans (pair-cong (to-terminal-unique _ _) ≈-refl) pair-ext0)

        sect-p₂ : ∀ {X Y} (h : prod 𝟙 X ⇒ Y) → ((h ∘ sect) ∘ p₂) ≈ h
        sect-p₂ h = tail-cancel sect-p₂-id


        fmor-μ-map : ∀ {j k} (P : Poly 𝒞 (suc j)) (δ : Fin j → obj) (Q : Poly 𝒞 (suc k)) (δ' : Fin k → obj)
                     (u : fobj μ-obj P (extend δ (μ-obj Q δ')) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ'))) →
                     ∀ {l} {R : Poly 𝒞 (suc l)} {ρ : Fin l → obj} →
                     (strong-fmor R (strong-extend-mor {δ = ρ} (λ i → p₂) (⦅_⦆ {P = P} {δ = δ} ((inMap Q δ' ∘ u) ∘ p₂))) ∘ sect)
                       ≈ fmor R (extend-mor (λ i → id (ρ i)) (μ-map P δ Q δ' u))
        fmor-μ-map P δ Q δ' u {R = R} =
          ∘-cong (strong-fmor-cong R (λ { Fin.zero → ≈-sym (sect-p₂ _) ; (Fin.suc i) → ≈-sym id-left })) ≈-refl

      μ-map-cong : ∀ {j k} (P : Poly 𝒞 (suc j)) (δ : Fin j → obj) (Q : Poly 𝒞 (suc k)) (δ' : Fin k → obj)
                   {u u' : fobj μ-obj P (extend δ (μ-obj Q δ')) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ'))} →
                   u ≈ u' → μ-map P δ Q δ' u ≈ μ-map P δ Q δ' u'
      μ-map-cong P δ Q δ' e = ∘-cong (⦅⦆-cong P δ (∘-cong (∘-cong ≈-refl e) ≈-refl)) ≈-refl

      μ-map-id : ∀ {j} (P : Poly 𝒞 (suc j)) (δ : Fin j → obj) → μ-map P δ P δ (id _) ≈ id _
      μ-map-id P δ =
        ≈-trans (∘-cong (≈-trans (⦅⦆-cong P δ (∘-cong id-right ≈-refl)) (⦅⦆-reflect P δ)) ≈-refl)
                (pair-p₂ _ _)

      μ-map-in : ∀ {j k} (P : Poly 𝒞 (suc j)) (δ : Fin j → obj) (Q : Poly 𝒞 (suc k)) (δ' : Fin k → obj)
                 (u : fobj μ-obj P (extend δ (μ-obj Q δ')) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ'))) →
                 (μ-map P δ Q δ' u ∘ inMap P δ)
                   ≈ (inMap Q δ' ∘ (u ∘ fmor P (extend-mor (λ i → id (δ i)) (μ-map P δ Q δ' u))))
      μ-map-in P δ Q δ' u =
        begin
          (fold-u ∘ sect) ∘ inMap P δ
        ≈⟨ tail-cong-assoc (sect-natural _) ⟩
          (fold-u ∘co (inMap P δ ∘ p₂)) ∘ sect
        ≈⟨ ∘-cong (≈-trans (⦅⦆-β {P = P} {δ = δ} alg) (tail-cong (pair-p₂ _ _))) ≈-refl ⟩
          ((inMap Q δ' ∘ u) ∘ strong-fmor P (strong-extend-mor (λ i → p₂) fold-u)) ∘ sect
        ≈⟨ tail-cong (fmor-μ-map P δ Q δ' u {R = P}) ⟩
          (inMap Q δ' ∘ u) ∘ fmor P (extend-mor (λ i → id (δ i)) (μ-map P δ Q δ' u))
        ≈⟨ assoc _ _ _ ⟩
          inMap Q δ' ∘ (u ∘ fmor P (extend-mor (λ i → id (δ i)) (μ-map P δ Q δ' u)))
        ∎
        where
          alg : prod (HasTerminal.witness 𝒞T) (fobj μ-obj P (extend δ (μ-obj Q δ'))) ⇒ μ-obj Q δ'
          alg = (inMap Q δ' ∘ u) ∘ p₂
          fold-u : prod (HasTerminal.witness 𝒞T) (μ-obj P δ) ⇒ μ-obj Q δ'
          fold-u = ⦅_⦆ {P = P} {δ = δ} alg
          open ≈-Reasoning isEquiv

      μ-map-comp : ∀ {i j k} (P : Poly 𝒞 (suc i)) (δ : Fin i → obj) (Q : Poly 𝒞 (suc j)) (δ' : Fin j → obj)
                   (R : Poly 𝒞 (suc k)) (δ'' : Fin k → obj)
                   (u  : fobj μ-obj P (extend δ (μ-obj Q δ')) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ')))
                   (v  : fobj μ-obj Q (extend δ' (μ-obj R δ'')) ⇒ fobj μ-obj R (extend δ'' (μ-obj R δ'')))
                   (u' : fobj μ-obj P (extend δ (μ-obj R δ'')) ⇒ fobj μ-obj Q (extend δ' (μ-obj R δ''))) →
                   (fmor Q (extend-mor (λ i → id (δ' i)) (μ-map Q δ' R δ'' v)) ∘ u)
                     ≈ (u' ∘ fmor P (extend-mor (λ i → id (δ i)) (μ-map Q δ' R δ'' v))) →
                   (μ-map Q δ' R δ'' v ∘ μ-map P δ Q δ' u) ≈ μ-map P δ R δ'' (v ∘ u')
      μ-map-comp P δ Q δ' R δ'' u v u' sq =
        ≈-trans (unitor-comp _ _) (∘-cong (fusion {P = P} {δ = δ} alg-u alg-vu' fold-v hyp) ≈-refl)
        where
          alg-u : prod 𝟙 (fobj μ-obj P (extend δ (μ-obj Q δ'))) ⇒ μ-obj Q δ'
          alg-u   = (inMap Q δ' ∘ u) ∘ p₂
          alg-v : prod 𝟙 (fobj μ-obj Q (extend δ' (μ-obj R δ''))) ⇒ μ-obj R δ''
          alg-v   = (inMap R δ'' ∘ v) ∘ p₂
          alg-vu' : prod 𝟙 (fobj μ-obj P (extend δ (μ-obj R δ''))) ⇒ μ-obj R δ''
          alg-vu' = (inMap R δ'' ∘ (v ∘ u')) ∘ p₂
          fold-v : prod 𝟙 (μ-obj Q δ') ⇒ μ-obj R δ''
          fold-v = ⦅_⦆ {P = Q} {δ = δ'} alg-v
          k = μ-map Q δ' R δ'' v

          step : (strong-fmor Q (strong-extend-mor (λ i → p₂) fold-v) ∘co (u ∘ p₂))
                   ≈ (u' ∘ strong-fmor P (strong-extend-mor (λ i → p₂) fold-v))
          step =
            begin
              SQ ∘ pair p₁ (u ∘ p₂)
            ≈˘⟨ ∘-cong ≈-refl (≈-trans (sect-pre _) (pair-cong (to-terminal-unique _ _) ≈-refl)) ⟩
              SQ ∘ (sect ∘ (u ∘ p₂))
            ≈˘⟨ ≈-trans (assoc _ _ _) (assoc _ _ _) ⟩
              ((SQ ∘ sect) ∘ u) ∘ p₂
            ≈⟨ ∘-cong (≈-trans (∘-cong (fmor-μ-map Q δ' R δ'' v {R = Q}) ≈-refl) sq) ≈-refl ⟩
              (u' ∘ fmor P (extend-mor (λ i → id (δ i)) k)) ∘ p₂
            ≈˘⟨ ∘-cong (∘-cong ≈-refl (fmor-μ-map Q δ' R δ'' v {R = P})) ≈-refl ⟩
              (u' ∘ (SP ∘ sect)) ∘ p₂
            ≈⟨ tail-cong (sect-p₂ SP) ⟩
              u' ∘ SP
            ∎
            where
              open ≈-Reasoning isEquiv
              SQ = strong-fmor Q (strong-extend-mor (λ i → p₂) fold-v)
              SP = strong-fmor P (strong-extend-mor (λ i → p₂) fold-v)

          hyp : (fold-v ∘co alg-u) ≈ (alg-vu' ∘co strong-fmor P (strong-extend-mor (λ i → p₂) fold-v))
          hyp =
            begin
              fold-v ∘co ((inMap Q δ' ∘ u) ∘ p₂)
            ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (assoc _ _ _)) ⟩
              fold-v ∘co (inMap Q δ' ∘ (u ∘ p₂))
            ≈˘⟨ ∘co-push fold-v (inMap Q δ') _ ⟩
              (fold-v ∘co (inMap Q δ' ∘ p₂)) ∘co (u ∘ p₂)
            ≈⟨ coKl.∘-cong (⦅⦆-β {P = Q} {δ = δ'} alg-v) ≈-refl ⟩
              (alg-v ∘co strong-fmor Q (strong-extend-mor (λ i → p₂) fold-v)) ∘co (u ∘ p₂)
            ≈⟨ coKl.assoc _ _ _ ⟩
              alg-v ∘co (strong-fmor Q (strong-extend-mor (λ i → p₂) fold-v) ∘co (u ∘ p₂))
            ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl step) ⟩
              alg-v ∘co (u' ∘ strong-fmor P (strong-extend-mor (λ i → p₂) fold-v))
            ≈⟨ tail-cong (pair-p₂ _ _) ⟩
              (inMap R δ'' ∘ v) ∘ (u' ∘ SP)
            ≈⟨ tail-cong-assoc (≈-sym (assoc _ _ _)) ⟩
              (inMap R δ'' ∘ (v ∘ u')) ∘ SP
            ≈˘⟨ tail-cong (pair-p₂ _ _) ⟩
              alg-vu' ∘co SP
            ∎
            where
              open ≈-Reasoning isEquiv
              SP = strong-fmor P (strong-extend-mor (λ i → p₂) fold-v)

      private
        strengthᵣ-sect : ∀ {X} → (strengthᵣ {𝟙} {X} ∘ sect) ≈ Lmap sect
        strengthᵣ-sect = begin
            strengthᵣ ∘ sect
          ≈˘⟨ id-left ⟩
            id _ ∘ (strengthᵣ ∘ sect)
          ≈˘⟨ ∘-cong (≈-trans (≈-sym (Lmap-comp _ _)) (≈-trans (Lmap-cong sect-p₂-id) Lmap-id)) ≈-refl ⟩
            (Lmap sect ∘ Lmap p₂) ∘ (strengthᵣ ∘ sect)
          ≈⟨ tail-cong (≈-sym (assoc _ _ _)) ⟩
            Lmap sect ∘ ((Lmap p₂ ∘ strengthᵣ) ∘ sect)
          ≈⟨ ∘-cong ≈-refl (≈-trans (∘-cong strengthᵣ-p₂ ≈-refl) (pair-p₂ _ _)) ⟩
            Lmap sect ∘ id _
          ≈⟨ id-right ⟩
            Lmap sect
          ∎ where open ≈-Reasoning isEquiv

        strengthᵣ-unit : ∀ {X} → strengthᵣ {𝟙} {X} ≈ (Lmap sect ∘ p₂)
        strengthᵣ-unit =
          ≈-trans (≈-sym id-right)
                  (≈-trans (∘-cong ≈-refl (≈-sym sect-p₂-id))
                           (head-cong strengthᵣ-sect))

        strong-Lmap-unit : ∀ {X Y} (h : prod 𝟙 X ⇒ Y) → strong-Lmap h ≈ (Lmap (h ∘ sect) ∘ p₂)
        strong-Lmap-unit h = ≈-trans (∘-cong ≈-refl strengthᵣ-unit) (head-cong (≈-sym (Lmap-comp _ _)))

        strong-prod-m-sect : ∀ {X₁ X₂ Y₁ Y₂} (f : prod 𝟙 X₁ ⇒ Y₁) (g : prod 𝟙 X₂ ⇒ Y₂) →
                             (strong-prod-m f g ∘ sect) ≈ prod-m (f ∘ sect) (g ∘ sect)
        strong-prod-m-sect f g =
          ≈-trans (pair-natural _ _ _)
                  (pair-cong (tail-cong-assoc (≈-sym (sect-natural p₁)))
                             (tail-cong-assoc (≈-sym (sect-natural p₂))))

        module CP = HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SC)

      fmor-const : ∀ {k} {A : obj} {δ δ' : Fin k → obj} (fs : ∀ i → δ i ⇒ δ' i) → fmor (const A) fs ≈ id A
      fmor-const fs = pair-p₂ _ _

      fmor-var : ∀ {k} (i : Fin k) {δ δ' : Fin k → obj} (fs : ∀ i → δ i ⇒ δ' i) → fmor (var i) fs ≈ fs i
      fmor-var i fs = tail-cancel (pair-p₂ _ _)

      fmor-+ : ∀ {k} (P Q : Poly 𝒞 k) {δ δ' : Fin k → obj} (fs : ∀ i → δ i ⇒ δ' i) →
               fmor (P + Q) fs ≈ CP.coprod-m (Lmap (fmor P fs)) (Lmap (fmor Q fs))
      fmor-+ P Q fs =
        ∘-cong (copair-cong (≈-trans (∘-cong ≈-refl (strong-Lmap-unit _)) (≈-sym (assoc _ _ _)))
                            (≈-trans (∘-cong ≈-refl (strong-Lmap-unit _)) (≈-sym (assoc _ _ _))))
               ≈-refl

      fmor-× : ∀ {k} (P Q : Poly 𝒞 k) {δ δ' : Fin k → obj} (fs : ∀ i → δ i ⇒ δ' i) →
               fmor (P × Q) fs ≈ Lmap (prod-m (fmor P fs) (fmor Q fs))
      fmor-× P Q fs =
        ≈-trans (∘-cong (strong-Lmap-unit _) ≈-refl)
                (≈-trans (tail-cancel (pair-p₂ _ _)) (Lmap-cong (strong-prod-m-sect _ _)))

      fmor-μ : ∀ {k} (P : Poly 𝒞 (suc k)) {δ δ' : Fin k → obj} (fs : ∀ i → δ i ⇒ δ' i) →
               fmor (μ P) fs ≈ μ-map P δ P δ' (fmor P (extend-mor fs (id _)))
      fmor-μ P {δ} {δ'} fs =
        ∘-cong (⦅⦆-cong P δ (≈-sym (tail-cong
                  (≈-trans (sect-p₂ _)
                           (strong-fmor-cong P (λ { Fin.zero → id-left ; (Fin.suc i) → ≈-refl }))))))
               ≈-refl

      private
        lift-p₂ : ∀ {Γ X} → (pair to-terminal (id _) ∘ p₂ {Γ} {X}) ≈ prod-m to-terminal (id _)
        lift-p₂ = ≈-trans (pair-natural _ _ _) (pair-cong (to-terminal-unique _ _) ≈-refl)

      strong-fmor-weaken : ∀ {k} {Γ : obj} (P : Poly 𝒞 k) {δ δ' : Fin k → obj} (gs : ∀ i → δ i ⇒ δ' i) →
                           strong-fmor {Γ = Γ} P (λ i → gs i ∘ p₂) ≈ (fmor P gs ∘ p₂)
      strong-fmor-weaken P gs =
        ≈-sym (begin
            (strong-fmor P (λ i → gs i ∘ p₂) ∘ pair to-terminal (id _)) ∘ p₂
          ≈⟨ assoc _ _ _ ⟩
            strong-fmor P (λ i → gs i ∘ p₂) ∘ (pair to-terminal (id _) ∘ p₂)
          ≈⟨ ∘-cong ≈-refl lift-p₂ ⟩
            strong-fmor P (λ i → gs i ∘ p₂) ∘ prod-m to-terminal (id _)
          ≈⟨ strong-fmor-reindex P to-terminal (λ i → gs i ∘ p₂) ⟩
            strong-fmor P (λ i → (gs i ∘ p₂) ∘ prod-m to-terminal (id _))
          ≈⟨ strong-fmor-cong P (λ i → tail-cong (≈-trans (pair-p₂ _ _) id-left)) ⟩
            strong-fmor P (λ i → gs i ∘ p₂)
          ∎)
        where open ≈-Reasoning isEquiv

      μ-map-weaken : ∀ {j k} {Γ : obj} (P : Poly 𝒞 (suc j)) (δ : Fin j → obj) (Q : Poly 𝒞 (suc k)) (δ' : Fin k → obj)
                     (u : fobj μ-obj P (extend δ (μ-obj Q δ')) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ'))) →
                     ⦅_⦆ {Γ = Γ} {P = P} {δ = δ} ((inMap Q δ' ∘ u) ∘ p₂) ≈ (μ-map P δ Q δ' u ∘ p₂)
      μ-map-weaken P δ Q δ' u =
        ≈-sym (begin
            (⦅_⦆ {P = P} {δ = δ} ((inMap Q δ' ∘ u) ∘ p₂) ∘ pair to-terminal (id _)) ∘ p₂
          ≈⟨ assoc _ _ _ ⟩
            ⦅_⦆ {P = P} {δ = δ} ((inMap Q δ' ∘ u) ∘ p₂) ∘ (pair to-terminal (id _) ∘ p₂)
          ≈⟨ ∘-cong ≈-refl lift-p₂ ⟩
            ⦅_⦆ {P = P} {δ = δ} ((inMap Q δ' ∘ u) ∘ p₂) ∘ prod-m to-terminal (id _)
          ≈⟨ ⦅⦆-reindex to-terminal _ ⟩
            ⦅ ((inMap Q δ' ∘ u) ∘ p₂) ∘ prod-m to-terminal (id _) ⦆
          ≈⟨ ⦅⦆-cong P δ (tail-cong (≈-trans (pair-p₂ _ _) id-left)) ⟩
            ⦅ (inMap Q δ' ∘ u) ∘ p₂ ⦆
          ∎)
        where open ≈-Reasoning isEquiv

Poly-map : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} →
           Functor 𝒞 𝒟 → ∀ {n} → Poly 𝒞 n → Poly 𝒟 n
Poly-map F (const A) = const (F .Functor.fobj A)
Poly-map F (var i)   = var i
Poly-map F (P + Q)   = Poly-map F P + Poly-map F Q
Poly-map F (P × Q)   = Poly-map F P × Poly-map F Q
Poly-map F (μ P)     = μ (Poly-map F P)

