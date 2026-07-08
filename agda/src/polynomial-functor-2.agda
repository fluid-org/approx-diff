{-# OPTIONS --prop --postfix-projections --safe #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; coKleisli-prod)
open import functor using (Functor)
open import prop-setoid using (module ≈-Reasoning)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym)

module polynomial-functor-2 where

data Poly {o m e} (𝒞 : Category o m e) (n : ℕ) : Set o where
  const : Category.obj 𝒞 → Poly 𝒞 n
  var   : Fin n → Poly 𝒞 n
  _+_   : Poly 𝒞 n → Poly 𝒞 n → Poly 𝒞 n
  _×_   : Poly 𝒞 n → Poly 𝒞 n → Poly 𝒞 n
  μ     : Poly 𝒞 (suc n) → Poly 𝒞 n

extend : ∀ {n} {ℓ} {A : Set ℓ} → (Fin n → A) → A → Fin (suc n) → A
extend δ x Fin.zero    = x
extend δ x (Fin.suc i) = δ i

-- Interpretation of the polynomials in a category with terminal object, products and strong coproducts.
module Interp
  {o m e} {𝒞 : Category o m e}
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
  where

  open Category 𝒞
  open HasProducts 𝒞P
  open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP)
  open HasStrongCoproducts 𝒞SCP using () renaming (copair to scopair)

  -- co-Kleisli notation: a morphism f : prod Γ X ⇒ Y lives in the co-Kleisli category for prod Γ -.
  infixl 21 _∘co_
  _∘co_ : ∀ {Γ X Y Z} → (prod Γ Y ⇒ Z) → (prod Γ X ⇒ Y) → (prod Γ X ⇒ Z)
  _∘co_ {Γ} = Category._∘_ (coKleisli-prod 𝒞P Γ)

  fobj : ∀ {n} → (μ-obj : ∀ {m} → Poly 𝒞 (suc m) → (Fin m → obj) → obj) → Poly 𝒞 n → (Fin n → obj) → obj
  fobj μ-obj (const A) δ = A
  fobj μ-obj (var i)   δ = δ i
  fobj μ-obj (P + Q)   δ = coprod (fobj μ-obj P δ) (fobj μ-obj Q δ)
  fobj μ-obj (P × Q)   δ = prod (fobj μ-obj P δ) (fobj μ-obj Q δ)
  fobj μ-obj (μ P)     δ = μ-obj P δ

  -- Parameterised initial algebras for the polynomials: carrier, algebra map and catamorphism, as
  -- operations only. The catamorphism is in context Γ (the open form avoids closure conversion, hence
  -- exponentials). The β/η laws live in HasMuLaws below, stated via the strong functorial action
  -- strong-fmor, which is defined from these operations; making the laws fields here would be circular.
  record HasMu : Set (o ⊔ m ⊔ e) where
    field
      μ-obj : ∀ {n} → Poly 𝒞 (suc n) → (Fin n → obj) → obj
      α     : ∀ {n} (P : Poly 𝒞 (suc n)) (δ : Fin n → obj) → fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
      ⦅_⦆  : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj} →
             (prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) → prod Γ (μ-obj P δ) ⇒ A

    open HasTerminal 𝒞T using (witness; to-terminal; to-terminal-unique)

    strong-extend-mor : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y} →
                 (∀ i → prod Γ (δ i) ⇒ δ' i) → (prod Γ X ⇒ Y) → ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
    strong-extend-mor fs x→y Fin.zero    = x→y
    strong-extend-mor fs x→y (Fin.suc i) = fs i

    mutual
      strong-fmor : ∀ {n Γ} (P : Poly 𝒞 n) {δ δ' : Fin n → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (fobj μ-obj P δ) ⇒ fobj μ-obj P δ'
      strong-fmor (const A) fs = p₂
      strong-fmor (var i)   fs = fs i
      strong-fmor (P + Q)   fs = scopair (in₁ ∘ strong-fmor P fs) (in₂ ∘ strong-fmor Q fs)
      strong-fmor (P × Q)   fs = strong-prod-m (strong-fmor P fs) (strong-fmor Q fs)
      strong-fmor (μ P)     fs = strong-μ-fmor P fs

      strong-μ-fmor : ∀ {n Γ} (P : Poly 𝒞 (suc n)) {δ δ' : Fin n → obj} →
                      (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
      strong-μ-fmor P {δ} {δ'} fs = ⦅ α P δ' ∘ strong-fmor P (strong-extend-mor fs p₂) ⦆

    fmor : ∀ {n} (P : Poly 𝒞 n) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → fobj μ-obj P δ ⇒ fobj μ-obj P δ'
    fmor P fs = strong-fmor P (λ i → fs i ∘ p₂) ∘ pair to-terminal (id _)

    -- A morphism between μ-objs, induced by an unfolding of P into Q at the target carrier.
    -- P, δ are explicit because fobj/μ-obj are not injective, so they can't be inferred from unfold.
    μ-map : ∀ {m n} (P : Poly 𝒞 (suc m)) (δ : Fin m → obj) (Q : Poly 𝒞 (suc n)) (δ' : Fin n → obj) →
            (fobj μ-obj P (extend δ (μ-obj Q δ')) ⇒ fobj μ-obj Q (extend δ' (μ-obj Q δ'))) →
            μ-obj P δ ⇒ μ-obj Q δ'
    μ-map P δ Q δ' unfold = ⦅_⦆ {P = P} {δ = δ} ((α Q δ' ∘ unfold) ∘ p₂) ∘ pair to-terminal (id _)

  -- The initiality laws for HasMu, stated via the strong functorial action derived from its operations.
  record HasMuLaws (Mu : HasMu) : Set (o ⊔ m ⊔ e) where
    open HasMu Mu
    field
      ⦅⦆-β : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) →
             (⦅ alg ⦆ ∘co (α P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) ⦅ alg ⦆))
      ⦅⦆-η : ∀ {n Γ A} {P : Poly 𝒞 (suc n)} {δ : Fin n → obj}
             (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) (h : prod Γ (μ-obj P δ) ⇒ A) →
             (h ∘co (α P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ i → p₂) h)) → h ≈ ⦅ alg ⦆

-- Action of a functor on polynomials: apply the functor at the const leaves.
Poly-map : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} →
           Functor 𝒞 𝒟 → ∀ {n} → Poly 𝒞 n → Poly 𝒟 n
Poly-map F (const A) = const (F .Functor.fobj A)
Poly-map F (var i)   = var i
Poly-map F (P + Q)   = Poly-map F P + Poly-map F Q
Poly-map F (P × Q)   = Poly-map F P × Poly-map F Q
Poly-map F (μ P)     = μ (Poly-map F P)

-- The functor preserves μ-types: each μ-object maps, up to isomorphism, to the
-- μ-object of the image polynomial in the image environment.
Preserves-μ : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
              (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
              (𝒟T : HasTerminal 𝒟) (𝒟P : HasProducts 𝒟) (𝒟SCP : HasStrongCoproducts 𝒟 𝒟P) →
              Interp.HasMu 𝒞T 𝒞P 𝒞SCP → Interp.HasMu 𝒟T 𝒟P 𝒟SCP → Functor 𝒞 𝒟 →
              Set (o₁ ⊔ m₂ ⊔ e₂)
Preserves-μ {𝒞 = 𝒞} {𝒟 = 𝒟} 𝒞T 𝒞P 𝒞SCP 𝒟T 𝒟P 𝒟SCP 𝒞Mu 𝒟Mu F =
  ∀ {n} (P : Poly 𝒞 (suc n)) (δ : Fin n → Category.obj 𝒞) →
  Category.Iso 𝒟 (F .Functor.fobj (CM.μ-obj P δ))
                 (DM.μ-obj (Poly-map F P) (λ i → F .Functor.fobj (δ i)))
  where
    module CM = Interp.HasMu 𝒞Mu
    module DM = Interp.HasMu 𝒟Mu

------------------------------------------------------------------------------
-- Componentwise morphisms between polynomials, their action on interpretations and μ-objects, and the functor
-- laws for that action, derived from the initiality laws. Componentwise isomorphic polynomials have isomorphic
-- μ-objects.
module MuIso
  {o m e} {𝒞 : Category o m e}
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
  (Mu : Interp.HasMu 𝒞T 𝒞P 𝒞SCP)
  (Laws : Interp.HasMuLaws 𝒞T 𝒞P 𝒞SCP Mu)
  where

  open Category 𝒞
  open HasProducts 𝒞P
  open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP) using (in₁; in₂)
  open HasStrongCoproducts 𝒞SCP using (copair-in₁; copair-in₂; copair-ext)
    renaming (copair to scopair; copair-cong to scopair-cong; copair-ext0 to scopair-ext0;
              copair-reindex to scopair-reindex)
  open HasTerminal 𝒞T using (to-terminal)
  open categories.Unitor 𝒞T 𝒞P using (sect; unitor-comp)
  open Interp 𝒞T 𝒞P 𝒞SCP
  open HasMu Mu
  open HasMuLaws Laws

  -- A componentwise morphism between two polynomials of the same shape: a
  -- morphism at each pair of const leaves.
  data PolyMor : ∀ {n} → Poly 𝒞 n → Poly 𝒞 n → Set (o ⊔ m) where
    const : ∀ {n A B} → A ⇒ B → PolyMor {n} (const A) (const B)
    var   : ∀ {n} (i : Fin n) → PolyMor (var i) (var i)
    _+_   : ∀ {n} {P P' Q Q' : Poly 𝒞 n} → PolyMor P P' → PolyMor Q Q' → PolyMor (P + Q) (P' + Q')
    _×_   : ∀ {n} {P P' Q Q' : Poly 𝒞 n} → PolyMor P P' → PolyMor Q Q' → PolyMor (P × Q) (P' × Q')
    μ     : ∀ {n} {P P' : Poly 𝒞 (suc n)} → PolyMor P P' → PolyMor (μ P) (μ P')

  -- Label composition and identity.
  _∙_ : ∀ {n} {P Q R : Poly 𝒞 n} → PolyMor Q R → PolyMor P Q → PolyMor P R
  const g ∙ const f = const (g ∘ f)
  var i   ∙ var .i  = var i
  (s + t) ∙ (r + u) = (s ∙ r) + (t ∙ u)
  (s × t) ∙ (r × u) = (s ∙ r) × (t ∙ u)
  μ s     ∙ μ r     = μ (s ∙ r)

  pm-id : ∀ {n} (P : Poly 𝒞 n) → PolyMor P P
  pm-id (const A) = const (id A)
  pm-id (var i)   = var i
  pm-id (P + Q)   = pm-id P + pm-id Q
  pm-id (P × Q)   = pm-id P × pm-id Q
  pm-id (μ P)     = μ (pm-id P)

  -- Pointwise equality of componentwise morphisms.
  data PolyMor-≈ : ∀ {n} {P Q : Poly 𝒞 n} → PolyMor P Q → PolyMor P Q → Prop (o ⊔ m ⊔ e) where
    const : ∀ {n A B} {f g : A ⇒ B} → f ≈ g → PolyMor-≈ {n} (const f) (const g)
    var   : ∀ {n} (i : Fin n) → PolyMor-≈ (var i) (var i)
    _+_   : ∀ {n} {P P' Q Q' : Poly 𝒞 n} {r r' : PolyMor P P'} {s s' : PolyMor Q Q'} →
            PolyMor-≈ r r' → PolyMor-≈ s s' → PolyMor-≈ (r + s) (r' + s')
    _×_   : ∀ {n} {P P' Q Q' : Poly 𝒞 n} {r r' : PolyMor P P'} {s s' : PolyMor Q Q'} →
            PolyMor-≈ r r' → PolyMor-≈ s s' → PolyMor-≈ (r × s) (r' × s')
    μ     : ∀ {n} {P P' : Poly 𝒞 (suc n)} {r r' : PolyMor P P'} →
            PolyMor-≈ r r' → PolyMor-≈ (μ r) (μ r')

  -- Componentwise isomorphism.
  record PolyIso {n} (P Q : Poly 𝒞 n) : Set (o ⊔ m ⊔ e) where
    field
      fwd     : PolyMor P Q
      bwd     : PolyMor Q P
      bwd∘fwd : PolyMor-≈ (bwd ∙ fwd) (pm-id P)
      fwd∘bwd : PolyMor-≈ (fwd ∙ bwd) (pm-id Q)

  -- Action of a componentwise morphism on interpretations and on μ-objects, in
  -- context Γ.
  mutual
    pm-fmor : ∀ {n Γ} {P Q : Poly 𝒞 n} → PolyMor P Q → {δ δ' : Fin n → obj} →
              (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (fobj μ-obj P δ) ⇒ fobj μ-obj Q δ'
    pm-fmor (const f) fs = f ∘ p₂
    pm-fmor (var i)   fs = fs i
    pm-fmor (r + s)   fs = scopair (in₁ ∘ pm-fmor r fs) (in₂ ∘ pm-fmor s fs)
    pm-fmor (r × s)   fs = strong-prod-m (pm-fmor r fs) (pm-fmor s fs)
    pm-fmor (μ r)     fs = pm-μ-fmor r fs

    pm-μ-fmor : ∀ {n Γ} {P Q : Poly 𝒞 (suc n)} → PolyMor P Q → {δ δ' : Fin n → obj} →
                (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj Q δ'
    pm-μ-fmor {Q = Q} r {δ} {δ'} fs = ⦅ α Q δ' ∘ pm-fmor r (strong-extend-mor fs p₂) ⦆

  -- The fold respects equality of algebras. P and δ are explicit because fobj/μ-obj are not injective, so
  -- can't be inferred from the algebras.
  ⦅⦆-cong : ∀ {n Γ A} (P : Poly 𝒞 (suc n)) (δ : Fin n → obj)
            {alg alg' : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A} →
            alg ≈ alg' → ⦅_⦆ {P = P} {δ = δ} alg ≈ ⦅_⦆ {P = P} {δ = δ} alg'
  ⦅⦆-cong P δ {alg = alg} {alg' = alg'} e =
    ⦅⦆-η {P = P} {δ = δ} alg' (⦅_⦆ {P = P} {δ = δ} alg)
      (≈-trans (⦅⦆-β {P = P} {δ = δ} alg)
        (∘-cong e ≈-refl))

  -- On identity labels the action is the strong functorial action.
  mutual
    pm-fmor-id : ∀ {n Γ} (P : Poly 𝒞 n) {δ δ' : Fin n → obj} (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                 pm-fmor (pm-id P) fs ≈ strong-fmor P fs
    pm-fmor-id (const A) fs = id-left
    pm-fmor-id (var i)   fs = ≈-refl
    pm-fmor-id (P + Q)   fs =
      scopair-cong (∘-cong ≈-refl (pm-fmor-id P fs)) (∘-cong ≈-refl (pm-fmor-id Q fs))
    pm-fmor-id (P × Q)   fs = strong-prod-m-cong (pm-fmor-id P fs) (pm-fmor-id Q fs)
    pm-fmor-id (μ P)     fs = pm-μ-fmor-id P fs

    pm-μ-fmor-id : ∀ {n Γ} (P : Poly 𝒞 (suc n)) {δ δ' : Fin n → obj} (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                   pm-μ-fmor (pm-id P) fs ≈ strong-μ-fmor P fs
    pm-μ-fmor-id P {δ} fs = ⦅⦆-cong P δ (∘-cong ≈-refl (pm-fmor-id P _))

  -- The action respects equality of labels and environments.
  mutual
    pm-fmor-cong : ∀ {n Γ} {P Q : Poly 𝒞 n} {r r' : PolyMor P Q} → PolyMor-≈ r r' →
                   {δ δ' : Fin n → obj} {fs fs' : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                   (∀ i → fs i ≈ fs' i) → pm-fmor r fs ≈ pm-fmor r' fs'
    pm-fmor-cong (const e) es = ∘-cong e ≈-refl
    pm-fmor-cong (var i)   es = es i
    pm-fmor-cong (e + e')  es =
      scopair-cong (∘-cong ≈-refl (pm-fmor-cong e es)) (∘-cong ≈-refl (pm-fmor-cong e' es))
    pm-fmor-cong (e × e')  es = strong-prod-m-cong (pm-fmor-cong e es) (pm-fmor-cong e' es)
    pm-fmor-cong (μ e)     es = pm-μ-fmor-cong e es

    pm-μ-fmor-cong : ∀ {n Γ} {P Q : Poly 𝒞 (suc n)} {r r' : PolyMor P Q} → PolyMor-≈ r r' →
                     {δ δ' : Fin n → obj} {fs fs' : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                     (∀ i → fs i ≈ fs' i) → pm-μ-fmor r fs ≈ pm-μ-fmor r' fs'
    pm-μ-fmor-cong {P = P} e {δ} es =
      ⦅⦆-cong P δ (∘-cong ≈-refl (pm-fmor-cong e (strong-extend-mor-cong es)))
      where
        strong-extend-mor-cong : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y}
          {fs fs' : ∀ i → prod Γ (δ i) ⇒ δ' i} {x : prod Γ X ⇒ Y} →
          (∀ i → fs i ≈ fs' i) → ∀ i → strong-extend-mor fs x i ≈ strong-extend-mor fs' x i
        strong-extend-mor-cong es Fin.zero    = ≈-refl
        strong-extend-mor-cong es (Fin.suc i) = es i

  pm-≈-refl : ∀ {n} {P Q : Poly 𝒞 n} (r : PolyMor P Q) → PolyMor-≈ r r
  pm-≈-refl (const f) = const ≈-refl
  pm-≈-refl (var i)   = var i
  pm-≈-refl (r + s)   = pm-≈-refl r + pm-≈-refl s
  pm-≈-refl (r × s)   = pm-≈-refl r × pm-≈-refl s
  pm-≈-refl (μ r)     = μ (pm-≈-refl r)

  ------------------------------------------------------------------------------
  -- Functor laws for the strong action, derived from the initiality laws.

  private
    module CoK {Γ : obj} = Category (coKleisli-prod 𝒞P Γ)

  pair-p₁-comp : ∀ {Γ X Y Z} (x : prod Γ X ⇒ Y) (y : prod Γ Z ⇒ X) →
                 (pair p₁ x ∘ pair p₁ y) ≈ pair p₁ (x ∘ pair p₁ y)
  pair-p₁-comp x y =
    begin
      pair p₁ x ∘ pair p₁ y
    ≈⟨ pair-natural _ _ _ ⟩
      pair (p₁ ∘ pair p₁ y) (x ∘ pair p₁ y)
    ≈⟨ pair-cong (pair-p₁ _ _) ≈-refl ⟩
      pair p₁ (x ∘ pair p₁ y)
    ∎ where open ≈-Reasoning isEquiv

  -- Push a plain morphism out of a co-Kleisli composite.
  ∘co-push : ∀ {Γ W X Y Z} (x : prod Γ Y ⇒ Z) (a : X ⇒ Y) (y : prod Γ W ⇒ X) →
             ((x ∘co (a ∘ p₂)) ∘co y) ≈ (x ∘co (a ∘ y))
  ∘co-push x a y =
    begin
      (x ∘ pair p₁ (a ∘ p₂)) ∘ pair p₁ y
    ≈⟨ assoc _ _ _ ⟩
      x ∘ (pair p₁ (a ∘ p₂) ∘ pair p₁ y)
    ≈⟨ ∘-cong ≈-refl (pair-p₁-comp _ _) ⟩
      x ∘ pair p₁ ((a ∘ p₂) ∘ pair p₁ y)
    ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (≈-trans (assoc _ _ _) (∘-cong ≈-refl (pair-p₂ _ _)))) ⟩
      x ∘ pair p₁ (a ∘ y)
    ∎ where open ≈-Reasoning isEquiv

  -- Composites of strong copairings of injections.
  scopair-comp : ∀ {Γ X₁ X₂ Y₁ Y₂ Z₁ Z₂}
    (f₂ : prod Γ Y₁ ⇒ Z₁) (g₂ : prod Γ Y₂ ⇒ Z₂) (f₁ : prod Γ X₁ ⇒ Y₁) (g₁ : prod Γ X₂ ⇒ Y₂) →
    (scopair (in₁ ∘ f₂) (in₂ ∘ g₂) ∘co scopair (in₁ ∘ f₁) (in₂ ∘ g₁))
      ≈ scopair (in₁ ∘ (f₂ ∘co f₁)) (in₂ ∘ (g₂ ∘co g₁))
  scopair-comp f₂ g₂ f₁ g₁ =
    ≈-trans (≈-sym (copair-ext _)) (scopair-cong branch₁ branch₂)
    where
      G = scopair (in₁ ∘ f₂) (in₂ ∘ g₂)
      F = scopair (in₁ ∘ f₁) (in₂ ∘ g₁)

      branch₁ : ((G ∘ pair p₁ F) ∘ pair p₁ (in₁ ∘ p₂)) ≈ (in₁ ∘ (f₂ ∘co f₁))
      branch₁ =
        begin
          (G ∘ pair p₁ F) ∘ pair p₁ (in₁ ∘ p₂)
        ≈⟨ assoc _ _ _ ⟩
          G ∘ (pair p₁ F ∘ pair p₁ (in₁ ∘ p₂))
        ≈⟨ ∘-cong ≈-refl (pair-p₁-comp _ _) ⟩
          G ∘ pair p₁ (F ∘ pair p₁ (in₁ ∘ p₂))
        ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (copair-in₁ _ _)) ⟩
          G ∘ pair p₁ (in₁ ∘ f₁)
        ≈˘⟨ ∘co-push G in₁ f₁ ⟩
          (G ∘ pair p₁ (in₁ ∘ p₂)) ∘ pair p₁ f₁
        ≈⟨ ∘-cong (copair-in₁ _ _) ≈-refl ⟩
          (in₁ ∘ f₂) ∘ pair p₁ f₁
        ≈⟨ assoc _ _ _ ⟩
          in₁ ∘ (f₂ ∘co f₁)
        ∎ where open ≈-Reasoning isEquiv

      branch₂ : ((G ∘ pair p₁ F) ∘ pair p₁ (in₂ ∘ p₂)) ≈ (in₂ ∘ (g₂ ∘co g₁))
      branch₂ =
        begin
          (G ∘ pair p₁ F) ∘ pair p₁ (in₂ ∘ p₂)
        ≈⟨ assoc _ _ _ ⟩
          G ∘ (pair p₁ F ∘ pair p₁ (in₂ ∘ p₂))
        ≈⟨ ∘-cong ≈-refl (pair-p₁-comp _ _) ⟩
          G ∘ pair p₁ (F ∘ pair p₁ (in₂ ∘ p₂))
        ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (copair-in₂ _ _)) ⟩
          G ∘ pair p₁ (in₂ ∘ g₁)
        ≈˘⟨ ∘co-push G in₂ g₁ ⟩
          (G ∘ pair p₁ (in₂ ∘ p₂)) ∘ pair p₁ g₁
        ≈⟨ ∘-cong (copair-in₂ _ _) ≈-refl ⟩
          (in₂ ∘ g₂) ∘ pair p₁ g₁
        ≈⟨ assoc _ _ _ ⟩
          in₂ ∘ (g₂ ∘co g₁)
        ∎ where open ≈-Reasoning isEquiv

  -- The strong action respects equality of environments.
  mutual
    strong-fmor-cong : ∀ {n Γ} (P : Poly 𝒞 n) {δ δ' : Fin n → obj}
                       {fs fs' : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                       (∀ i → fs i ≈ fs' i) → strong-fmor P fs ≈ strong-fmor P fs'
    strong-fmor-cong (const A) es = ≈-refl
    strong-fmor-cong (var i)   es = es i
    strong-fmor-cong (P + Q)   es =
      scopair-cong (∘-cong ≈-refl (strong-fmor-cong P es)) (∘-cong ≈-refl (strong-fmor-cong Q es))
    strong-fmor-cong (P × Q)   es = strong-prod-m-cong (strong-fmor-cong P es) (strong-fmor-cong Q es)
    strong-fmor-cong (μ P)     es = strong-μ-fmor-cong P es

    strong-μ-fmor-cong : ∀ {n Γ} (P : Poly 𝒞 (suc n)) {δ δ' : Fin n → obj}
                         {fs fs' : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                         (∀ i → fs i ≈ fs' i) → strong-μ-fmor P fs ≈ strong-μ-fmor P fs'
    strong-μ-fmor-cong P {δ} {δ'} {fs} {fs'} es =
      ⦅⦆-cong P δ (∘-cong ≈-refl (strong-fmor-cong P sem-es))
      where
        sem-es : ∀ i → strong-extend-mor fs p₂ i ≈ strong-extend-mor fs' p₂ i
        sem-es Fin.zero    = ≈-refl
        sem-es (Fin.suc i) = es i

  -- Pointwise co-Kleisli composition of extended environments is the extension
  -- of the composites.
  strong-extend-mor-comp : ∀ {n Γ} {δ δ' δ'' : Fin n → obj} {X Y Z}
    {as : ∀ i → prod Γ (δ' i) ⇒ δ'' i} {bs : ∀ i → prod Γ (δ i) ⇒ δ' i} {cs : ∀ i → prod Γ (δ i) ⇒ δ'' i}
    {x : prod Γ Y ⇒ Z} {y : prod Γ X ⇒ Y} {z : prod Γ X ⇒ Z} →
    (∀ i → (as i ∘co bs i) ≈ cs i) → ((x ∘co y) ≈ z) →
    ∀ i → (strong-extend-mor as x i ∘co strong-extend-mor bs y i) ≈ strong-extend-mor cs z i
  strong-extend-mor-comp es ez Fin.zero    = ez
  strong-extend-mor-comp es ez (Fin.suc i) = es i

  -- The strong action is functorial: composites of actions are actions of
  -- pointwise co-Kleisli composites.
  mutual
    strong-fmor-comp : ∀ {n Γ} (P : Poly 𝒞 n) {δ δ' δ'' : Fin n → obj}
                       (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                       (strong-fmor P gs ∘co strong-fmor P fs) ≈ strong-fmor P (λ i → gs i ∘co fs i)
    strong-fmor-comp (const A) gs fs = CoK.id-left
    strong-fmor-comp (var i)   gs fs = ≈-refl
    strong-fmor-comp (P + Q)   gs fs =
      ≈-trans (scopair-comp _ _ _ _)
              (scopair-cong (∘-cong ≈-refl (strong-fmor-comp P gs fs))
                            (∘-cong ≈-refl (strong-fmor-comp Q gs fs)))
    strong-fmor-comp (P × Q)   gs fs =
      ≈-trans (strong-prod-m-comp _ _ _ _)
              (strong-prod-m-cong (strong-fmor-comp P gs fs) (strong-fmor-comp Q gs fs))
    strong-fmor-comp (μ P)     gs fs = strong-μ-fmor-comp P gs fs

    strong-μ-fmor-comp : ∀ {n Γ} (P : Poly 𝒞 (suc n)) {δ δ' δ'' : Fin n → obj}
                         (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                         (strong-μ-fmor P gs ∘co strong-μ-fmor P fs) ≈ strong-μ-fmor P (λ i → gs i ∘co fs i)
    strong-μ-fmor-comp P {δ} {δ'} {δ''} gs fs =
      ⦅⦆-η {P = P} {δ = δ} alg (μ-gs ∘co μ-fs) chain
      where
        μ-gs = strong-μ-fmor P gs
        μ-fs = strong-μ-fmor P fs
        alg-f = α P δ' ∘ strong-fmor P (strong-extend-mor fs p₂)
        alg-g = α P δ'' ∘ strong-fmor P (strong-extend-mor gs p₂)
        alg = α P δ'' ∘ strong-fmor P (strong-extend-mor (λ i → gs i ∘co fs i) p₂)

        head : (μ-gs ∘co alg-f) ≈ (alg-g ∘co strong-fmor P (strong-extend-mor fs μ-gs))
        head =
          begin
            μ-gs ∘co (α P δ' ∘ strong-fmor P (strong-extend-mor fs p₂))
          ≈˘⟨ ∘co-push μ-gs (α P δ') _ ⟩
            (μ-gs ∘co (α P δ' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor fs p₂)
          ≈⟨ CoK.∘-cong (⦅⦆-β {P = P} {δ = δ'} alg-g) ≈-refl ⟩
            (alg-g ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs)) ∘co strong-fmor P (strong-extend-mor fs p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            alg-g ∘co (strong-fmor P (strong-extend-mor (λ _ → p₂) μ-gs) ∘co strong-fmor P (strong-extend-mor fs p₂))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _) (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-left) CoK.id-right))) ⟩
            alg-g ∘co strong-fmor P (strong-extend-mor fs μ-gs)
          ∎ where open ≈-Reasoning isEquiv

        chain : ((μ-gs ∘co μ-fs) ∘co (α P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-gs ∘co μ-fs)))
        chain =
          begin
            (μ-gs ∘co μ-fs) ∘co (α P δ ∘ p₂)
          ≈⟨ CoK.assoc μ-gs μ-fs (α P δ ∘ p₂) ⟩
            μ-gs ∘co (μ-fs ∘co (α P δ ∘ p₂))
          ≈⟨ CoK.∘-cong ≈-refl (⦅⦆-β {P = P} {δ = δ} alg-f) ⟩
            μ-gs ∘co (alg-f ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-fs))
          ≈˘⟨ CoK.assoc μ-gs alg-f _ ⟩
            (μ-gs ∘co alg-f) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-fs)
          ≈⟨ CoK.∘-cong head ≈-refl ⟩
            (alg-g ∘co strong-fmor P (strong-extend-mor fs μ-gs)) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-fs)
          ≈⟨ CoK.assoc _ _ _ ⟩
            alg-g ∘co (strong-fmor P (strong-extend-mor fs μ-gs) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-fs))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _) (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-right) ≈-refl))) ⟩
            alg-g ∘co strong-fmor P (strong-extend-mor fs (μ-gs ∘co μ-fs))
          ≈⟨ assoc _ _ _ ⟩
            α P δ'' ∘ (strong-fmor P (strong-extend-mor gs p₂) ∘co strong-fmor P (strong-extend-mor fs (μ-gs ∘co μ-fs)))
          ≈⟨ ∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _) (strong-fmor-cong P (strong-extend-mor-comp (λ _ → ≈-refl) CoK.id-left))) ⟩
            α P δ'' ∘ strong-fmor P (strong-extend-mor (λ j → gs j ∘co fs j) (μ-gs ∘co μ-fs))
          ≈˘⟨ ∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _) (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-right) CoK.id-left))) ⟩
            α P δ'' ∘ (strong-fmor P (strong-extend-mor (λ j → gs j ∘co fs j) p₂) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-gs ∘co μ-fs)))
          ≈˘⟨ assoc _ _ _ ⟩
            alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-gs ∘co μ-fs))
          ∎ where open ≈-Reasoning isEquiv

  -- The strong action interchanges with the componentwise action: post- or
  -- pre-composing a strong action is absorbed into the environments.
  mutual
    pm-fmor-post : ∀ {n Γ} {P Q : Poly 𝒞 n} (r : PolyMor P Q) {δ δ' δ'' : Fin n → obj}
                   (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                   (strong-fmor Q gs ∘co pm-fmor r fs) ≈ pm-fmor r (λ i → gs i ∘co fs i)
    pm-fmor-post (const f) gs fs = CoK.id-left
    pm-fmor-post (var i)   gs fs = ≈-refl
    pm-fmor-post (r + s)   gs fs =
      ≈-trans (scopair-comp _ _ _ _)
              (scopair-cong (∘-cong ≈-refl (pm-fmor-post r gs fs))
                            (∘-cong ≈-refl (pm-fmor-post s gs fs)))
    pm-fmor-post (r × s)   gs fs =
      ≈-trans (strong-prod-m-comp _ _ _ _)
              (strong-prod-m-cong (pm-fmor-post r gs fs) (pm-fmor-post s gs fs))
    pm-fmor-post (μ r)     gs fs = pm-μ-fmor-post r gs fs

    pm-fmor-pre : ∀ {n Γ} {P Q : Poly 𝒞 n} (r : PolyMor P Q) {δ δ' δ'' : Fin n → obj}
                  (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                  (pm-fmor r gs ∘co strong-fmor P fs) ≈ pm-fmor r (λ i → gs i ∘co fs i)
    pm-fmor-pre (const f) gs fs = CoK.id-right
    pm-fmor-pre (var i)   gs fs = ≈-refl
    pm-fmor-pre (r + s)   gs fs =
      ≈-trans (scopair-comp _ _ _ _)
              (scopair-cong (∘-cong ≈-refl (pm-fmor-pre r gs fs))
                            (∘-cong ≈-refl (pm-fmor-pre s gs fs)))
    pm-fmor-pre (r × s)   gs fs =
      ≈-trans (strong-prod-m-comp _ _ _ _)
              (strong-prod-m-cong (pm-fmor-pre r gs fs) (pm-fmor-pre s gs fs))
    pm-fmor-pre (μ r)     gs fs = pm-μ-fmor-pre r gs fs

    pm-μ-fmor-post : ∀ {n Γ} {P Q : Poly 𝒞 (suc n)} (r : PolyMor P Q) {δ δ' δ'' : Fin n → obj}
                     (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                     (strong-μ-fmor Q gs ∘co pm-μ-fmor r fs) ≈ pm-μ-fmor r (λ i → gs i ∘co fs i)
    pm-μ-fmor-post {P = P} {Q = Q} r {δ} {δ'} {δ''} gs fs =
      ⦅⦆-η {P = P} {δ = δ} alg (μ-gs ∘co μ-r) chain
      where
        μ-gs = strong-μ-fmor Q gs
        μ-r = pm-μ-fmor r fs
        alg-r = α Q δ' ∘ pm-fmor r (strong-extend-mor fs p₂)
        alg-g = α Q δ'' ∘ strong-fmor Q (strong-extend-mor gs p₂)
        alg = α Q δ'' ∘ pm-fmor r (strong-extend-mor (λ i → gs i ∘co fs i) p₂)

        head : (μ-gs ∘co alg-r) ≈ (alg-g ∘co pm-fmor r (strong-extend-mor fs μ-gs))
        head =
          begin
            μ-gs ∘co (α Q δ' ∘ pm-fmor r (strong-extend-mor fs p₂))
          ≈˘⟨ ∘co-push μ-gs (α Q δ') _ ⟩
            (μ-gs ∘co (α Q δ' ∘ p₂)) ∘co pm-fmor r (strong-extend-mor fs p₂)
          ≈⟨ CoK.∘-cong (⦅⦆-β {P = Q} {δ = δ'} alg-g) ≈-refl ⟩
            (alg-g ∘co strong-fmor Q (strong-extend-mor (λ _ → p₂) μ-gs)) ∘co pm-fmor r (strong-extend-mor fs p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            alg-g ∘co (strong-fmor Q (strong-extend-mor (λ _ → p₂) μ-gs) ∘co pm-fmor r (strong-extend-mor fs p₂))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (pm-fmor-post r _ _) (pm-fmor-cong (pm-≈-refl r) (strong-extend-mor-comp (λ _ → CoK.id-left) CoK.id-right))) ⟩
            alg-g ∘co pm-fmor r (strong-extend-mor fs μ-gs)
          ∎ where open ≈-Reasoning isEquiv

        chain : ((μ-gs ∘co μ-r) ∘co (α P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-gs ∘co μ-r)))
        chain =
          begin
            (μ-gs ∘co μ-r) ∘co (α P δ ∘ p₂)
          ≈⟨ CoK.assoc μ-gs μ-r (α P δ ∘ p₂) ⟩
            μ-gs ∘co (μ-r ∘co (α P δ ∘ p₂))
          ≈⟨ CoK.∘-cong ≈-refl (⦅⦆-β {P = P} {δ = δ} alg-r) ⟩
            μ-gs ∘co (alg-r ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r))
          ≈˘⟨ CoK.assoc μ-gs alg-r _ ⟩
            (μ-gs ∘co alg-r) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r)
          ≈⟨ CoK.∘-cong head ≈-refl ⟩
            (alg-g ∘co pm-fmor r (strong-extend-mor fs μ-gs)) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r)
          ≈⟨ CoK.assoc _ _ _ ⟩
            alg-g ∘co (pm-fmor r (strong-extend-mor fs μ-gs) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (pm-fmor-pre r _ _) (pm-fmor-cong (pm-≈-refl r) (strong-extend-mor-comp (λ _ → CoK.id-right) ≈-refl))) ⟩
            alg-g ∘co pm-fmor r (strong-extend-mor fs (μ-gs ∘co μ-r))
          ≈⟨ assoc _ _ _ ⟩
            α Q δ'' ∘ (strong-fmor Q (strong-extend-mor gs p₂) ∘co pm-fmor r (strong-extend-mor fs (μ-gs ∘co μ-r)))
          ≈⟨ ∘-cong ≈-refl (≈-trans (pm-fmor-post r _ _) (pm-fmor-cong (pm-≈-refl r) (strong-extend-mor-comp (λ _ → ≈-refl) CoK.id-left))) ⟩
            α Q δ'' ∘ pm-fmor r (strong-extend-mor (λ j → gs j ∘co fs j) (μ-gs ∘co μ-r))
          ≈˘⟨ ∘-cong ≈-refl (≈-trans (pm-fmor-pre r _ _) (pm-fmor-cong (pm-≈-refl r) (strong-extend-mor-comp (λ _ → CoK.id-right) CoK.id-left))) ⟩
            α Q δ'' ∘ (pm-fmor r (strong-extend-mor (λ j → gs j ∘co fs j) p₂) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-gs ∘co μ-r)))
          ≈˘⟨ assoc _ _ _ ⟩
            alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-gs ∘co μ-r))
          ∎ where open ≈-Reasoning isEquiv

    pm-μ-fmor-pre : ∀ {n Γ} {P Q : Poly 𝒞 (suc n)} (r : PolyMor P Q) {δ δ' δ'' : Fin n → obj}
                    (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                    (pm-μ-fmor r gs ∘co strong-μ-fmor P fs) ≈ pm-μ-fmor r (λ i → gs i ∘co fs i)
    pm-μ-fmor-pre {P = P} {Q = Q} r {δ} {δ'} {δ''} gs fs =
      ⦅⦆-η {P = P} {δ = δ} alg (μ-r ∘co μ-fs) chain
      where
        μ-r = pm-μ-fmor r gs
        μ-fs = strong-μ-fmor P fs
        alg-f = α P δ' ∘ strong-fmor P (strong-extend-mor fs p₂)
        alg-r = α Q δ'' ∘ pm-fmor r (strong-extend-mor gs p₂)
        alg = α Q δ'' ∘ pm-fmor r (strong-extend-mor (λ i → gs i ∘co fs i) p₂)

        head : (μ-r ∘co alg-f) ≈ (alg-r ∘co strong-fmor P (strong-extend-mor fs μ-r))
        head =
          begin
            μ-r ∘co (α P δ' ∘ strong-fmor P (strong-extend-mor fs p₂))
          ≈˘⟨ ∘co-push μ-r (α P δ') _ ⟩
            (μ-r ∘co (α P δ' ∘ p₂)) ∘co strong-fmor P (strong-extend-mor fs p₂)
          ≈⟨ CoK.∘-cong (⦅⦆-β {P = P} {δ = δ'} alg-r) ≈-refl ⟩
            (alg-r ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r)) ∘co strong-fmor P (strong-extend-mor fs p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            alg-r ∘co (strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r) ∘co strong-fmor P (strong-extend-mor fs p₂))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _) (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-left) CoK.id-right))) ⟩
            alg-r ∘co strong-fmor P (strong-extend-mor fs μ-r)
          ∎ where open ≈-Reasoning isEquiv

        chain : ((μ-r ∘co μ-fs) ∘co (α P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-r ∘co μ-fs)))
        chain =
          begin
            (μ-r ∘co μ-fs) ∘co (α P δ ∘ p₂)
          ≈⟨ CoK.assoc μ-r μ-fs (α P δ ∘ p₂) ⟩
            μ-r ∘co (μ-fs ∘co (α P δ ∘ p₂))
          ≈⟨ CoK.∘-cong ≈-refl (⦅⦆-β {P = P} {δ = δ} alg-f) ⟩
            μ-r ∘co (alg-f ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-fs))
          ≈˘⟨ CoK.assoc μ-r alg-f _ ⟩
            (μ-r ∘co alg-f) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-fs)
          ≈⟨ CoK.∘-cong head ≈-refl ⟩
            (alg-r ∘co strong-fmor P (strong-extend-mor fs μ-r)) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-fs)
          ≈⟨ CoK.assoc _ _ _ ⟩
            alg-r ∘co (strong-fmor P (strong-extend-mor fs μ-r) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-fs))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _) (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-right) ≈-refl))) ⟩
            alg-r ∘co strong-fmor P (strong-extend-mor fs (μ-r ∘co μ-fs))
          ≈⟨ assoc _ _ _ ⟩
            α Q δ'' ∘ (pm-fmor r (strong-extend-mor gs p₂) ∘co strong-fmor P (strong-extend-mor fs (μ-r ∘co μ-fs)))
          ≈⟨ ∘-cong ≈-refl (≈-trans (pm-fmor-pre r _ _) (pm-fmor-cong (pm-≈-refl r) (strong-extend-mor-comp (λ _ → ≈-refl) CoK.id-left))) ⟩
            α Q δ'' ∘ pm-fmor r (strong-extend-mor (λ j → gs j ∘co fs j) (μ-r ∘co μ-fs))
          ≈˘⟨ ∘-cong ≈-refl (≈-trans (pm-fmor-pre r _ _) (pm-fmor-cong (pm-≈-refl r) (strong-extend-mor-comp (λ _ → CoK.id-right) CoK.id-left))) ⟩
            α Q δ'' ∘ (pm-fmor r (strong-extend-mor (λ j → gs j ∘co fs j) p₂) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-r ∘co μ-fs)))
          ≈˘⟨ assoc _ _ _ ⟩
            alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-r ∘co μ-fs))
          ∎ where open ≈-Reasoning isEquiv

  -- The componentwise action is functorial: composites of actions are actions
  -- of composite labels and pointwise co-Kleisli composite environments.
  mutual
    pm-fmor-comp : ∀ {n Γ} {P Q R : Poly 𝒞 n} (s : PolyMor Q R) (r : PolyMor P Q) {δ δ' δ'' : Fin n → obj}
                   (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                   (pm-fmor s gs ∘co pm-fmor r fs) ≈ pm-fmor (s ∙ r) (λ i → gs i ∘co fs i)
    pm-fmor-comp (const g) (const f) gs fs =
      ≈-trans (assoc _ _ _) (≈-trans (∘-cong ≈-refl (pair-p₂ _ _)) (≈-sym (assoc _ _ _)))
    pm-fmor-comp (var i)   (var .i)  gs fs = ≈-refl
    pm-fmor-comp (s + t)   (r + u)   gs fs =
      ≈-trans (scopair-comp _ _ _ _)
              (scopair-cong (∘-cong ≈-refl (pm-fmor-comp s r gs fs))
                            (∘-cong ≈-refl (pm-fmor-comp t u gs fs)))
    pm-fmor-comp (s × t)   (r × u)   gs fs =
      ≈-trans (strong-prod-m-comp _ _ _ _)
              (strong-prod-m-cong (pm-fmor-comp s r gs fs) (pm-fmor-comp t u gs fs))
    pm-fmor-comp (μ s)     (μ r)     gs fs = pm-μ-fmor-comp s r gs fs

    pm-μ-fmor-comp : ∀ {n Γ} {P Q R : Poly 𝒞 (suc n)} (s : PolyMor Q R) (r : PolyMor P Q) {δ δ' δ'' : Fin n → obj}
                     (gs : ∀ i → prod Γ (δ' i) ⇒ δ'' i) (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                     (pm-μ-fmor s gs ∘co pm-μ-fmor r fs) ≈ pm-μ-fmor (s ∙ r) (λ i → gs i ∘co fs i)
    pm-μ-fmor-comp {P = P} {Q = Q} {R = R} s r {δ} {δ'} {δ''} gs fs =
      ⦅⦆-η {P = P} {δ = δ} alg (μ-s ∘co μ-r) chain
      where
        μ-s = pm-μ-fmor s gs
        μ-r = pm-μ-fmor r fs
        alg-r = α Q δ' ∘ pm-fmor r (strong-extend-mor fs p₂)
        alg-s = α R δ'' ∘ pm-fmor s (strong-extend-mor gs p₂)
        alg = α R δ'' ∘ pm-fmor (s ∙ r) (strong-extend-mor (λ i → gs i ∘co fs i) p₂)

        head : (μ-s ∘co alg-r) ≈ (alg-s ∘co pm-fmor r (strong-extend-mor fs μ-s))
        head =
          begin
            μ-s ∘co (α Q δ' ∘ pm-fmor r (strong-extend-mor fs p₂))
          ≈˘⟨ ∘co-push μ-s (α Q δ') _ ⟩
            (μ-s ∘co (α Q δ' ∘ p₂)) ∘co pm-fmor r (strong-extend-mor fs p₂)
          ≈⟨ CoK.∘-cong (⦅⦆-β {P = Q} {δ = δ'} alg-s) ≈-refl ⟩
            (alg-s ∘co strong-fmor Q (strong-extend-mor (λ _ → p₂) μ-s)) ∘co pm-fmor r (strong-extend-mor fs p₂)
          ≈⟨ CoK.assoc _ _ _ ⟩
            alg-s ∘co (strong-fmor Q (strong-extend-mor (λ _ → p₂) μ-s) ∘co pm-fmor r (strong-extend-mor fs p₂))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (pm-fmor-post r _ _) (pm-fmor-cong (pm-≈-refl r) (strong-extend-mor-comp (λ _ → CoK.id-left) CoK.id-right))) ⟩
            alg-s ∘co pm-fmor r (strong-extend-mor fs μ-s)
          ∎ where open ≈-Reasoning isEquiv

        chain : ((μ-s ∘co μ-r) ∘co (α P δ ∘ p₂)) ≈ (alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-s ∘co μ-r)))
        chain =
          begin
            (μ-s ∘co μ-r) ∘co (α P δ ∘ p₂)
          ≈⟨ CoK.assoc μ-s μ-r (α P δ ∘ p₂) ⟩
            μ-s ∘co (μ-r ∘co (α P δ ∘ p₂))
          ≈⟨ CoK.∘-cong ≈-refl (⦅⦆-β {P = P} {δ = δ} alg-r) ⟩
            μ-s ∘co (alg-r ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r))
          ≈˘⟨ CoK.assoc μ-s alg-r _ ⟩
            (μ-s ∘co alg-r) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r)
          ≈⟨ CoK.∘-cong head ≈-refl ⟩
            (alg-s ∘co pm-fmor r (strong-extend-mor fs μ-s)) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r)
          ≈⟨ CoK.assoc _ _ _ ⟩
            alg-s ∘co (pm-fmor r (strong-extend-mor fs μ-s) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) μ-r))
          ≈⟨ CoK.∘-cong ≈-refl (≈-trans (pm-fmor-pre r _ _) (pm-fmor-cong (pm-≈-refl r) (strong-extend-mor-comp (λ _ → CoK.id-right) ≈-refl))) ⟩
            alg-s ∘co pm-fmor r (strong-extend-mor fs (μ-s ∘co μ-r))
          ≈⟨ assoc _ _ _ ⟩
            α R δ'' ∘ (pm-fmor s (strong-extend-mor gs p₂) ∘co pm-fmor r (strong-extend-mor fs (μ-s ∘co μ-r)))
          ≈⟨ ∘-cong ≈-refl (≈-trans (pm-fmor-comp s r _ _) (pm-fmor-cong (pm-≈-refl (s ∙ r)) (strong-extend-mor-comp (λ _ → ≈-refl) CoK.id-left))) ⟩
            α R δ'' ∘ pm-fmor (s ∙ r) (strong-extend-mor (λ j → gs j ∘co fs j) (μ-s ∘co μ-r))
          ≈˘⟨ ∘-cong ≈-refl (≈-trans (pm-fmor-pre (s ∙ r) _ _) (pm-fmor-cong (pm-≈-refl (s ∙ r)) (strong-extend-mor-comp (λ _ → CoK.id-right) CoK.id-left))) ⟩
            α R δ'' ∘ (pm-fmor (s ∙ r) (strong-extend-mor (λ j → gs j ∘co fs j) p₂) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-s ∘co μ-r)))
          ≈˘⟨ assoc _ _ _ ⟩
            alg ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) (μ-s ∘co μ-r))
          ∎ where open ≈-Reasoning isEquiv

  -- On identity environments the strong action is the identity.
  mutual
    strong-fmor-p₂ : ∀ {n Γ} (P : Poly 𝒞 n) {δ : Fin n → obj} →
                     strong-fmor {Γ = Γ} P {δ} {δ} (λ i → p₂) ≈ p₂
    strong-fmor-p₂ (const A) = ≈-refl
    strong-fmor-p₂ (var i)   = ≈-refl
    strong-fmor-p₂ (P + Q)   =
      ≈-trans (scopair-cong (∘-cong ≈-refl (strong-fmor-p₂ P)) (∘-cong ≈-refl (strong-fmor-p₂ Q)))
              scopair-ext0
    strong-fmor-p₂ (P × Q)   =
      ≈-trans (strong-prod-m-cong (strong-fmor-p₂ P) (strong-fmor-p₂ Q))
              (≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _)) (pair-ext _))
    strong-fmor-p₂ (μ P)     = strong-μ-fmor-p₂ P

    strong-μ-fmor-p₂ : ∀ {n Γ} (P : Poly 𝒞 (suc n)) {δ : Fin n → obj} →
                       strong-μ-fmor {Γ = Γ} P {δ} {δ} (λ i → p₂) ≈ p₂
    strong-μ-fmor-p₂ P {δ} =
      ≈-sym (⦅⦆-η {P = P} {δ = δ} alg₀ p₂ premise)
      where
        alg₀ : prod _ (fobj μ-obj P (extend δ (μ-obj P δ))) ⇒ μ-obj P δ
        alg₀ = α P δ ∘ strong-fmor P (strong-extend-mor {X = μ-obj P δ} {Y = μ-obj P δ} (λ _ → p₂) p₂)

        es₀ : ∀ i → strong-extend-mor {X = μ-obj P δ} {Y = μ-obj P δ} (λ _ → p₂) p₂ i ≈ p₂
        es₀ Fin.zero    = ≈-refl
        es₀ (Fin.suc i) = ≈-refl

        rhs : (alg₀ ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) p₂)) ≈ (α P δ ∘ p₂)
        rhs =
          begin
            alg₀ ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) p₂)
          ≈⟨ assoc _ _ _ ⟩
            α P δ ∘ (strong-fmor P (strong-extend-mor (λ _ → p₂) p₂) ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) p₂))
          ≈⟨ ∘-cong ≈-refl (≈-trans (strong-fmor-comp P _ _) (strong-fmor-cong P (strong-extend-mor-comp (λ _ → CoK.id-left) CoK.id-left))) ⟩
            α P δ ∘ strong-fmor P (strong-extend-mor (λ _ → p₂) p₂)
          ≈⟨ ∘-cong ≈-refl (strong-fmor-cong P es₀) ⟩
            α P δ ∘ strong-fmor P (λ i → p₂)
          ≈⟨ ∘-cong ≈-refl (strong-fmor-p₂ P) ⟩
            α P δ ∘ p₂
          ∎ where open ≈-Reasoning isEquiv

        premise : (p₂ ∘co (α P δ ∘ p₂)) ≈ (alg₀ ∘co strong-fmor P (strong-extend-mor (λ _ → p₂) p₂))
        premise = ≈-trans CoK.id-left (≈-sym rhs)

  -- Componentwise isomorphic polynomials have isomorphic μ-objects.
  pm-μ-iso : ∀ {n} {P Q : Poly 𝒞 (suc n)} (r : PolyIso P Q) {δ δ' : Fin n → obj} →
             (es : ∀ i → Iso (δ i) (δ' i)) → Iso (μ-obj P δ) (μ-obj Q δ')
  pm-μ-iso {P = P} {Q = Q} r {δ} {δ'} es = record
    { fwd = pm-μ-fmor (r .PolyIso.fwd) (λ i → es i .Iso.fwd ∘ p₂) ∘ sect
    ; bwd = pm-μ-fmor (r .PolyIso.bwd) (λ i → es i .Iso.bwd ∘ p₂) ∘ sect
    ; fwd∘bwd≈id = roundtrip Q (r .PolyIso.bwd) (r .PolyIso.fwd) (r .PolyIso.fwd∘bwd)
                     (λ i → es i .Iso.bwd) (λ i → es i .Iso.fwd) (λ i → es i .Iso.fwd∘bwd≈id)
    ; bwd∘fwd≈id = roundtrip P (r .PolyIso.fwd) (r .PolyIso.bwd) (r .PolyIso.bwd∘fwd)
                     (λ i → es i .Iso.fwd) (λ i → es i .Iso.bwd) (λ i → es i .Iso.bwd∘fwd≈id)
    }
    where
      roundtrip : ∀ {n} (A : Poly 𝒞 (suc n)) {B : Poly 𝒞 (suc n)} {δA δB : Fin n → obj}
                  (u : PolyMor A B) (v : PolyMor B A) → PolyMor-≈ (v ∙ u) (pm-id A) →
                  (us : ∀ i → δA i ⇒ δB i) (vs : ∀ i → δB i ⇒ δA i) → (∀ i → (vs i ∘ us i) ≈ id (δA i)) →
                  ((pm-μ-fmor v (λ i → vs i ∘ p₂) ∘ sect) ∘ (pm-μ-fmor u (λ i → us i ∘ p₂) ∘ sect)) ≈ id (μ-obj A δA)
      roundtrip A {B} {δA} {δB} u v vu us vs law =
        ≈-trans (unitor-comp _ _)
        (≈-trans (∘-cong (pm-μ-fmor-comp v u _ _) ≈-refl)
        (≈-trans (∘-cong (pm-μ-fmor-cong vu env-law) ≈-refl)
        (≈-trans (∘-cong (pm-μ-fmor-id A _) ≈-refl)
        (≈-trans (∘-cong (strong-μ-fmor-p₂ A) ≈-refl)
                 (pair-p₂ _ _)))))
        where
          env-law : ∀ i → ((vs i ∘ p₂) ∘co (us i ∘ p₂)) ≈ p₂
          env-law i =
            begin
              (vs i ∘ p₂) ∘ pair p₁ (us i ∘ p₂)
            ≈⟨ assoc _ _ _ ⟩
              vs i ∘ (p₂ ∘ pair p₁ (us i ∘ p₂))
            ≈⟨ ∘-cong ≈-refl (pair-p₂ _ _) ⟩
              vs i ∘ (us i ∘ p₂)
            ≈˘⟨ assoc _ _ _ ⟩
              (vs i ∘ us i) ∘ p₂
            ≈⟨ ∘-cong (law i) ≈-refl ⟩
              id _ ∘ p₂
            ≈⟨ id-left ⟩
              p₂
            ∎ where open ≈-Reasoning isEquiv

  -- Congruences for componentwise isomorphisms.
  pm-iso-const : ∀ {n A B} → Iso A B → PolyIso {n} (const A) (const B)
  pm-iso-const i .PolyIso.fwd     = const (i .Iso.fwd)
  pm-iso-const i .PolyIso.bwd     = const (i .Iso.bwd)
  pm-iso-const i .PolyIso.bwd∘fwd = const (i .Iso.bwd∘fwd≈id)
  pm-iso-const i .PolyIso.fwd∘bwd = const (i .Iso.fwd∘bwd≈id)

  pm-iso-var : ∀ {n} (i : Fin n) → PolyIso (var i) (var i)
  pm-iso-var i .PolyIso.fwd     = var i
  pm-iso-var i .PolyIso.bwd     = var i
  pm-iso-var i .PolyIso.bwd∘fwd = var i
  pm-iso-var i .PolyIso.fwd∘bwd = var i

  pm-iso-sum : ∀ {n} {P P' Q Q' : Poly 𝒞 n} → PolyIso P P' → PolyIso Q Q' → PolyIso (P + Q) (P' + Q')
  pm-iso-sum r s .PolyIso.fwd     = r .PolyIso.fwd + s .PolyIso.fwd
  pm-iso-sum r s .PolyIso.bwd     = r .PolyIso.bwd + s .PolyIso.bwd
  pm-iso-sum r s .PolyIso.bwd∘fwd = r .PolyIso.bwd∘fwd + s .PolyIso.bwd∘fwd
  pm-iso-sum r s .PolyIso.fwd∘bwd = r .PolyIso.fwd∘bwd + s .PolyIso.fwd∘bwd

  pm-iso-prod : ∀ {n} {P P' Q Q' : Poly 𝒞 n} → PolyIso P P' → PolyIso Q Q' → PolyIso (P × Q) (P' × Q')
  pm-iso-prod r s .PolyIso.fwd     = r .PolyIso.fwd × s .PolyIso.fwd
  pm-iso-prod r s .PolyIso.bwd     = r .PolyIso.bwd × s .PolyIso.bwd
  pm-iso-prod r s .PolyIso.bwd∘fwd = r .PolyIso.bwd∘fwd × s .PolyIso.bwd∘fwd
  pm-iso-prod r s .PolyIso.fwd∘bwd = r .PolyIso.fwd∘bwd × s .PolyIso.fwd∘bwd

  pm-iso-μ : ∀ {n} {P P' : Poly 𝒞 (suc n)} → PolyIso P P' → PolyIso (μ P) (μ P')
  pm-iso-μ r .PolyIso.fwd     = μ (r .PolyIso.fwd)
  pm-iso-μ r .PolyIso.bwd     = μ (r .PolyIso.bwd)
  pm-iso-μ r .PolyIso.bwd∘fwd = μ (r .PolyIso.bwd∘fwd)
  pm-iso-μ r .PolyIso.fwd∘bwd = μ (r .PolyIso.fwd∘bwd)

  -- Reindexing the context of the strong action and of catamorphisms:
  -- precomposition with prod-m u id commutes with both.
  ⦅⦆-reindex : ∀ {n Γ Γ' A} (P : Poly 𝒞 (suc n)) (δ : Fin n → obj) (u : Γ' ⇒ Γ)
               (alg : prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) →
               (⦅_⦆ {P = P} {δ = δ} alg ∘ prod-m u (id _)) ≈ ⦅_⦆ {P = P} {δ = δ} (alg ∘ prod-m u (id _))

  strong-fmor-reindex : ∀ {n Γ Γ'} (P : Poly 𝒞 n) {δ δ' : Fin n → obj} (u : Γ' ⇒ Γ)
                        (fs : ∀ i → prod Γ (δ i) ⇒ δ' i) →
                        (strong-fmor P fs ∘ prod-m u (id _)) ≈ strong-fmor P (λ i → fs i ∘ prod-m u (id _))

  strong-fmor-reindex (const A) u fs = ≈-trans (pair-p₂ _ _) id-left
  strong-fmor-reindex (var i)   u fs = ≈-refl
  strong-fmor-reindex (P + Q)   u fs =
    ≈-trans (scopair-reindex u _ _)
      (scopair-cong
        (≈-trans (assoc _ _ _) (∘-cong ≈-refl (strong-fmor-reindex P u fs)))
        (≈-trans (assoc _ _ _) (∘-cong ≈-refl (strong-fmor-reindex Q u fs))))
  strong-fmor-reindex (P × Q)   u fs =
    ≈-trans (∘-cong ≈-refl (prod-m-cong ≈-refl (≈-sym prod-m-id)))
      (≈-trans (strong-prod-m-pre _ _ _ _ _)
        (strong-prod-m-cong (strong-fmor-reindex P u fs) (strong-fmor-reindex Q u fs)))
  strong-fmor-reindex (μ P) {δ} {δ'} u fs =
    ≈-trans (⦅⦆-reindex P δ u _)
      (⦅⦆-cong P δ
        (≈-trans (assoc _ _ _)
          (∘-cong ≈-refl
            (≈-trans (strong-fmor-reindex P u (strong-extend-mor fs p₂))
              (strong-fmor-cong P pointwise)))))
    where
      pointwise : ∀ i → (strong-extend-mor fs p₂ i ∘ prod-m u (id _))
                        ≈ strong-extend-mor (λ j → fs j ∘ prod-m u (id _)) p₂ i
      pointwise Fin.zero    = ≈-trans (pair-p₂ _ _) id-left
      pointwise (Fin.suc i) = ≈-refl

  ⦅⦆-reindex {n} {Γ} {Γ'} {A} P δ u alg =
    ⦅⦆-η {P = P} {δ = δ} (alg ∘ prod-m u (id _)) (⦅_⦆ {P = P} {δ = δ} alg ∘ prod-m u (id _)) sq
    where
      h = ⦅_⦆ {P = P} {δ = δ} alg ∘ prod-m u (id _)

      pointwise : ∀ i → (strong-extend-mor (λ j → p₂) (⦅_⦆ {P = P} {δ = δ} alg) i ∘ prod-m u (id _))
                        ≈ strong-extend-mor (λ j → p₂) h i
      pointwise Fin.zero    = ≈-refl
      pointwise (Fin.suc i) = ≈-trans (pair-p₂ _ _) id-left

      lhs-chain : (h ∘co (α P δ ∘ p₂)) ≈ (alg ∘ pair (u ∘ p₁) (strong-fmor P (strong-extend-mor (λ i → p₂) h)))
      lhs-chain =
        begin
          (⦅_⦆ {P = P} {δ = δ} alg ∘ prod-m u (id _)) ∘ pair p₁ (α P δ ∘ p₂)
        ≈⟨ assoc _ _ _ ⟩
          ⦅_⦆ {P = P} {δ = δ} alg ∘ (prod-m u (id _) ∘ pair p₁ (α P δ ∘ p₂))
        ≈⟨ ∘-cong ≈-refl (prodm-pair-interchange u (α P δ)) ⟩
          ⦅_⦆ {P = P} {δ = δ} alg ∘ (pair p₁ (α P δ ∘ p₂) ∘ prod-m u (id _))
        ≈˘⟨ assoc _ _ _ ⟩
          (⦅_⦆ {P = P} {δ = δ} alg ∘ pair p₁ (α P δ ∘ p₂)) ∘ prod-m u (id _)
        ≈⟨ ∘-cong (⦅⦆-β alg) ≈-refl ⟩
          (alg ∘ pair p₁ (strong-fmor P (strong-extend-mor (λ i → p₂) (⦅_⦆ {P = P} {δ = δ} alg)))) ∘ prod-m u (id _)
        ≈⟨ assoc _ _ _ ⟩
          alg ∘ (pair p₁ (strong-fmor P (strong-extend-mor (λ i → p₂) (⦅_⦆ {P = P} {δ = δ} alg))) ∘ prod-m u (id _))
        ≈⟨ ∘-cong ≈-refl (pair-natural _ _ _) ⟩
          alg ∘ pair (p₁ ∘ prod-m u (id _)) (strong-fmor P (strong-extend-mor (λ i → p₂) (⦅_⦆ {P = P} {δ = δ} alg)) ∘ prod-m u (id _))
        ≈⟨ ∘-cong ≈-refl (pair-cong (pair-p₁ _ _) (≈-trans (strong-fmor-reindex P u _) (strong-fmor-cong P pointwise))) ⟩
          alg ∘ pair (u ∘ p₁) (strong-fmor P (strong-extend-mor (λ i → p₂) h))
        ∎ where open ≈-Reasoning isEquiv


      rhs-chain : ((alg ∘ prod-m u (id _)) ∘co strong-fmor P (strong-extend-mor (λ i → p₂) h))
                  ≈ (alg ∘ pair (u ∘ p₁) (strong-fmor P (strong-extend-mor (λ i → p₂) h)))
      rhs-chain =
        begin
          (alg ∘ prod-m u (id _)) ∘ pair p₁ (strong-fmor P (strong-extend-mor (λ i → p₂) h))
        ≈⟨ assoc _ _ _ ⟩
          alg ∘ (prod-m u (id _) ∘ pair p₁ (strong-fmor P (strong-extend-mor (λ i → p₂) h)))
        ≈⟨ ∘-cong ≈-refl (pair-compose _ _ _ _) ⟩
          alg ∘ pair (u ∘ p₁) (id _ ∘ strong-fmor P (strong-extend-mor (λ i → p₂) h))
        ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
          alg ∘ pair (u ∘ p₁) (strong-fmor P (strong-extend-mor (λ i → p₂) h))
        ∎ where open ≈-Reasoning isEquiv

      sq : (h ∘co (α P δ ∘ p₂)) ≈ ((alg ∘ prod-m u (id _)) ∘co strong-fmor P (strong-extend-mor (λ i → p₂) h))
      sq = ≈-trans lhs-chain (≈-sym rhs-chain)

  -- Constant abstraction: a rigid correspondence between a polynomial and a
  -- form of it in which some constants have been replaced by variables (and
  -- possibly vice versa), over given environments. Rigid: the leaf conditions
  -- are equalities of objects, so the induced comparisons need no morphism
  -- families.
  data Abs : ∀ {n n'} (δ : Fin n → obj) (δ' : Fin n' → obj) →
             Poly 𝒞 n → Poly 𝒞 n' → Set (o ⊔ m) where
    var   : ∀ {n n'} {δ : Fin n → obj} {δ' : Fin n' → obj} {i j} →
            δ' j ≡ δ i → Abs δ δ' (var i) (var j)
    const : ∀ {n n'} {δ : Fin n → obj} {δ' : Fin n' → obj} {A} →
            Abs δ δ' (const A) (const A)
    cabs  : ∀ {n n'} {δ : Fin n → obj} {δ' : Fin n' → obj} {A j} →
            δ' j ≡ A → Abs δ δ' (const A) (var j)
    cconc : ∀ {n n'} {δ : Fin n → obj} {δ' : Fin n' → obj} {A i} →
            δ i ≡ A → Abs δ δ' (var i) (const A)
    _+_   : ∀ {n n'} {δ : Fin n → obj} {δ' : Fin n' → obj} {P P' Q Q'} →
            Abs δ δ' P P' → Abs δ δ' Q Q' → Abs δ δ' (P + Q) (P' + Q')
    _×_   : ∀ {n n'} {δ : Fin n → obj} {δ' : Fin n' → obj} {P P' Q Q'} →
            Abs δ δ' P P' → Abs δ δ' Q Q' → Abs δ δ' (P × Q) (P' × Q')
    μ     : ∀ {n n'} {δ : Fin n → obj} {δ' : Fin n' → obj} {P P'} →
            (∀ X → Abs (extend δ X) (extend δ' X) P P') →
            Abs δ δ' (μ P) (μ P')

  -- The correspondence is symmetric.
  Abs-sym : ∀ {n n'} {δ : Fin n → obj} {δ' : Fin n' → obj} {P P'} →
            Abs δ δ' P P' → Abs δ' δ P' P
  Abs-sym (var eq)   = var (≡-sym eq)
  Abs-sym const      = const
  Abs-sym (cabs eq)  = cconc eq
  Abs-sym (cconc eq) = cabs eq
  Abs-sym (r + s)    = Abs-sym r + Abs-sym s
  Abs-sym (r × s)    = Abs-sym r × Abs-sym s
  Abs-sym (μ r)      = μ (λ X → Abs-sym (r X))

  -- Every polynomial corresponds to itself.
  Abs-refl : ∀ {n} {δ : Fin n → obj} (P : Poly 𝒞 n) → Abs δ δ P P
  Abs-refl (const A) = const
  Abs-refl (var i)   = var ≡-refl
  Abs-refl (P + Q)   = Abs-refl P + Abs-refl Q
  Abs-refl (P × Q)   = Abs-refl P × Abs-refl Q
  Abs-refl (μ P)     = μ (λ X → Abs-refl P)
