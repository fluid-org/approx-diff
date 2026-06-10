{-# OPTIONS --prop --postfix-projections --allow-unsolved-metas #-}

import Data.Fin as Fin
open Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (_⊔_)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts;
         strong-coproducts→coproducts; coKleisli-prod)
open import functor using (Functor; StrongFunctor)
open import product-category using (_^_)
open import prop-setoid using (module ≈-Reasoning)

module polynomial-functor-2
  {o m e} {𝒞 : Category o m e}
  (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞) (𝒞SCP : HasStrongCoproducts 𝒞 𝒞P)
  (T-strong : StrongFunctor 𝒞P) where

open Category 𝒞
open HasProducts 𝒞P
open HasCoproducts (strong-coproducts→coproducts 𝒞T 𝒞SCP)
open HasStrongCoproducts 𝒞SCP using () renaming (copair to scopair; copair-cong to scopair-cong)
open StrongFunctor T-strong using (right-strength; right-strength-p₂; right-strength-natural) renaming (F to T)

-- co-Kleisli notation: a morphism f : prod Γ X ⇒ Y lives in the co-Kleisli category for prod Γ -.
-- _∘co_ is composition there; id-co is the identity (p₂). Re-exported for use in HasMu laws.
infixl 21 _∘co_
_∘co_ : ∀ {Γ X Y Z} → (prod Γ Y ⇒ Z) → (prod Γ X ⇒ Y) → (prod Γ X ⇒ Z)
_∘co_ {Γ} = Category._∘_ (coKleisli-prod 𝒞P Γ)

id-co : ∀ {Γ X} → prod Γ X ⇒ X
id-co = p₂

module _ {Γ : obj} where
  open Category (coKleisli-prod 𝒞P Γ) public using ()
    renaming (assoc to assoc-co;
              ∘-cong to ∘-cong-co; ∘-cong₁ to ∘-cong-co₁; ∘-cong₂ to ∘-cong-co₂;
              id-left to id-left-co; id-right to id-right-co)

data Poly (n : ℕ) : Set o where
  const : obj → Poly n
  var   : Fin n → Poly n
  _+_   : Poly n → Poly n → Poly n
  _×_   : Poly n → Poly n → Poly n
  μ     : Poly (suc n) → Poly n
  T∘_   : Poly n → Poly n

extend : ∀ {n} → (Fin n → obj) → obj → Fin (suc n) → obj
extend δ A Fin.zero    = A
extend δ A (Fin.suc i) = δ i

fobj : ∀ {n} → (μ-obj : ∀ {m} → Poly (suc m) → (Fin m → obj) → obj) → Poly n → (Fin n → obj) → obj
fobj μ-obj (const A) δ = A
fobj μ-obj (var i)   δ = δ i
fobj μ-obj (P + Q)   δ = coprod (fobj μ-obj P δ) (fobj μ-obj Q δ)
fobj μ-obj (P × Q)   δ = prod (fobj μ-obj P δ) (fobj μ-obj Q δ)
fobj μ-obj (μ P)     δ = μ-obj P δ
fobj μ-obj (T∘ P)    δ = Functor.fobj T (fobj μ-obj P δ)

-- Use a Mendler-style catamorphism (Mendler 1991, "Inductive types and type constraints
-- in the second-order lambda calculus") which abstracts over the recursive carrier, so β/η can be stated
-- without reference to a functorial action; otherwise things get circular. Usual ⦅_⦆ is then derived.
record HasMu : Set (o ⊔ m ⊔ e) where
  field
    μ-obj : ∀ {n} → Poly (suc n) → (Fin n → obj) → obj
    α     : ∀ {n} (P : Poly (suc n)) (δ : Fin n → obj) → fobj μ-obj P (extend δ (μ-obj P δ)) ⇒ μ-obj P δ
    ⦅_⦆ᴹ : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
          (∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A)) → prod Γ (μ-obj P δ) ⇒ A
    ⦅⦆ᴹ-β : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
           (step : ∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A)) →
           (⦅ step ⦆ᴹ ∘co (α P δ ∘ p₂)) ≈ step (μ-obj P δ) ⦅ step ⦆ᴹ
    ⦅⦆ᴹ-η : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
           (step : ∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A))
           (h : prod Γ (μ-obj P δ) ⇒ A) → (h ∘co (α P δ ∘ p₂)) ≈ step (μ-obj P δ) h → h ≈ ⦅ step ⦆ᴹ

  open HasTerminal 𝒞T using (witness; to-terminal; to-terminal-unique)

  ⦅_⦆ᴹ-cong : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj}
              {step₁ step₂ : ∀ X → (prod Γ X ⇒ A) → (prod Γ (fobj μ-obj P (extend δ X)) ⇒ A)} →
              (∀ X (x→A : prod Γ X ⇒ A) → step₁ X x→A ≈ step₂ X x→A) → ⦅ step₁ ⦆ᴹ ≈ ⦅ step₂ ⦆ᴹ
  ⦅_⦆ᴹ-cong {P = P} {δ = δ} {step₁ = step₁} {step₂ = step₂} step₁≈step₂ =
    ⦅⦆ᴹ-η {P = P} {δ = δ} step₂ ⦅ step₁ ⦆ᴹ
      (≈-trans (⦅⦆ᴹ-β {P = P} {δ = δ} step₁) (step₁≈step₂ (μ-obj P δ) ⦅ step₁ ⦆ᴹ))

  extend-mor : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y} →
               (∀ i → prod Γ (δ i) ⇒ δ' i) → (prod Γ X ⇒ Y) → ∀ i → prod Γ (extend δ X i) ⇒ extend δ' Y i
  extend-mor fs x→y Fin.zero    = x→y
  extend-mor fs x→y (Fin.suc i) = fs i

  mutual
    strong-fmor : ∀ {n Γ} (P : Poly n) {δ δ' : Fin n → obj} →
                  (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (fobj μ-obj P δ) ⇒ fobj μ-obj P δ'
    strong-fmor (const A) fs = p₂
    strong-fmor (var i)   fs = fs i
    strong-fmor (P + Q)   fs = scopair (in₁ ∘ strong-fmor P fs) (in₂ ∘ strong-fmor Q fs)
    strong-fmor (P × Q)   fs = pair (strong-fmor P fs ∘ pair p₁ (p₁ ∘ p₂))
                                    (strong-fmor Q fs ∘ pair p₁ (p₂ ∘ p₂))
    strong-fmor (μ P)     fs = strong-μ-fmor P fs
    strong-fmor (T∘ P)    fs = Functor.fmor T (strong-fmor P fs) ∘ right-strength

    strong-μ-fmor : ∀ {n Γ} (P : Poly (suc n)) {δ δ' : Fin n → obj} →
                    (∀ i → prod Γ (δ i) ⇒ δ' i) → prod Γ (μ-obj P δ) ⇒ μ-obj P δ'
    strong-μ-fmor P {δ} {δ'} fs = ⦅ step ⦆ᴹ
      where
        step : ∀ X → (prod _ X ⇒ μ-obj P δ') → prod _ (fobj μ-obj P (extend δ X)) ⇒ μ-obj P δ'
        step X x→μ' = α P δ' ∘ strong-fmor P (extend-mor fs x→μ')

  extend-mor-cong : ∀ {n Γ} {δ δ' : Fin n → obj} {X Y}
                    {fs gs : ∀ i → prod Γ (δ i) ⇒ δ' i} {x→y : prod Γ X ⇒ Y} →
                    (∀ i → fs i ≈ gs i) → ∀ i → extend-mor fs x→y i ≈ extend-mor gs x→y i
  extend-mor-cong fs≈gs Fin.zero    = ≈-refl
  extend-mor-cong fs≈gs (Fin.suc i) = fs≈gs i

  mutual
    strong-fmor-cong : ∀ {n Γ} (P : Poly n) {δ δ' : Fin n → obj}
                       {fs gs : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                       (∀ i → fs i ≈ gs i) → strong-fmor P fs ≈ strong-fmor P gs
    strong-fmor-cong (const A) fs≈gs = ≈-refl
    strong-fmor-cong (var i)   fs≈gs = fs≈gs i
    strong-fmor-cong (P + Q)   fs≈gs =
      scopair-cong (∘-cong ≈-refl (strong-fmor-cong P fs≈gs)) (∘-cong ≈-refl (strong-fmor-cong Q fs≈gs))
    strong-fmor-cong (P × Q)   fs≈gs =
      pair-cong (∘-cong (strong-fmor-cong P fs≈gs) ≈-refl) (∘-cong (strong-fmor-cong Q fs≈gs) ≈-refl)
    strong-fmor-cong (μ P)     fs≈gs = strong-μ-fmor-cong P fs≈gs
    strong-fmor-cong (T∘ P)    fs≈gs = ∘-cong (Functor.fmor-cong T (strong-fmor-cong P fs≈gs)) ≈-refl

    strong-μ-fmor-cong : ∀ {n Γ} (P : Poly (suc n)) {δ δ' : Fin n → obj}
                         {fs gs : ∀ i → prod Γ (δ i) ⇒ δ' i} →
                         (∀ i → fs i ≈ gs i) → strong-μ-fmor P fs ≈ strong-μ-fmor P gs
    strong-μ-fmor-cong P {δ} {δ'} fs≈gs = ⦅_⦆ᴹ-cong λ X x→μ' →
      ∘-cong ≈-refl (strong-fmor-cong P (extend-mor-cong fs≈gs))

  scopair-p₂ : ∀ {Γ x y} → scopair (in₁ ∘ p₂ {Γ} {x}) (in₂ ∘ p₂ {Γ} {y}) ≈ p₂
  scopair-p₂ =
    ≈-trans (scopair-cong (≈-sym (pair-p₂ _ _)) (≈-sym (pair-p₂ _ _)))
            (HasStrongCoproducts.copair-ext 𝒞SCP p₂)

  extend-mor-p₂ : ∀ {n Γ} {δ : Fin n → obj} {X} →
                  ∀ i → extend-mor {δ = δ} {δ' = δ} (λ _ → p₂) (p₂ {Γ} {X}) i ≈ p₂
  extend-mor-p₂ Fin.zero    = ≈-refl
  extend-mor-p₂ (Fin.suc i) = ≈-refl

  mutual
    strong-fmor-id : ∀ {n Γ} (P : Poly n) {δ : Fin n → obj} →
                     strong-fmor {Γ = Γ} P {δ = δ} {δ' = δ} (λ _ → p₂) ≈ p₂
    strong-fmor-id (const A) = ≈-refl
    strong-fmor-id (var i) = ≈-refl
    strong-fmor-id (P + Q) =
      ≈-trans (scopair-cong (∘-cong ≈-refl (strong-fmor-id P)) (∘-cong ≈-refl (strong-fmor-id Q))) scopair-p₂
    strong-fmor-id (P × Q) =
      ≈-trans (pair-cong (∘-cong (strong-fmor-id P) ≈-refl) (∘-cong (strong-fmor-id Q) ≈-refl))
              (≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _)) (pair-ext _))
    strong-fmor-id (μ P) = strong-μ-fmor-id P
    strong-fmor-id (T∘ P) =
      ≈-trans (∘-cong (Functor.fmor-cong T (strong-fmor-id P)) ≈-refl) right-strength-p₂

    strong-μ-fmor-id : ∀ {n Γ} (P : Poly (suc n)) {δ : Fin n → obj} →
                       strong-μ-fmor {Γ = Γ} P {δ = δ} {δ' = δ} (λ _ → p₂) ≈ p₂
    strong-μ-fmor-id P {δ} =
      ≈-sym (⦅⦆ᴹ-η _ p₂
        (≈-trans (pair-p₂ _ _)
                 (≈-sym (∘-cong ≈-refl (≈-trans (strong-fmor-cong P extend-mor-p₂) (strong-fmor-id P))))))

  fmor : ∀ {n} (P : Poly n) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → fobj μ-obj P δ ⇒ fobj μ-obj P δ'
  fmor P fs = strong-fmor P (λ i → fs i ∘ p₂) ∘ pair to-terminal (id _)

  μ-fmor : ∀ {n} (P : Poly (suc n)) {δ δ' : Fin n → obj} → (∀ i → δ i ⇒ δ' i) → μ-obj P δ ⇒ μ-obj P δ'
  μ-fmor P fs = strong-μ-fmor P (λ i → fs i ∘ p₂) ∘ pair to-terminal (id _)

  ⦅_⦆ : ∀ {n Γ A} {P : Poly (suc n)} {δ : Fin n → obj} →
        (prod Γ (fobj μ-obj P (extend δ A)) ⇒ A) → prod Γ (μ-obj P δ) ⇒ A
  ⦅_⦆ {Γ = Γ} {A = A} {P = P} {δ = δ} alg = ⦅ step ⦆ᴹ
    where
      step : ∀ X → (prod Γ X ⇒ A) → prod Γ (fobj μ-obj P (extend δ X)) ⇒ A
      step X x→A = alg ∘ pair p₁ (strong-fmor P (extend-mor (λ _ → p₂) x→A))

  -- Carrier-shaped morphism family: f at position 0, id at positions 1..n.
  extend-fam : ∀ {n} {δ : Fin n → obj} {X Y} → (X ⇒ Y) → ∀ i → extend δ X i ⇒ extend δ Y i
  extend-fam f Fin.zero    = f
  extend-fam f (Fin.suc i) = id _

  -- Initial algebras of pointwise-isomorphic functors are isomorphic.
  μ-obj-resp : ∀ {m n} {P : Poly (suc m)} {δ : Fin m → obj} {Q : Poly (suc n)} {δ' : Fin n → obj}
               (unfold-iso : ∀ X → Iso (fobj μ-obj P (extend δ X)) (fobj μ-obj Q (extend δ' X))) →
               (unfold-natural : ∀ {X Y} (f : X ⇒ Y) →
                                 (fmor Q (extend-fam f) ∘ Iso.fwd (unfold-iso X)) ≈
                                 (Iso.fwd (unfold-iso Y) ∘ fmor P (extend-fam f))) →
               Iso (μ-obj P δ) (μ-obj Q δ')
  μ-obj-resp {P = P} {δ = δ} {Q = Q} {δ' = δ'} unfold-iso unfold-natural = iso
    where
      step-fwd : ∀ X → (prod witness X ⇒ μ-obj Q δ') → prod witness (fobj μ-obj P (extend δ X)) ⇒ μ-obj Q δ'
      step-fwd X x→μ' =
        α Q δ' ∘ fmor Q (extend-fam (x→μ' ∘ pair to-terminal (id _))) ∘ Iso.fwd (unfold-iso X) ∘ p₂

      step-bwd : ∀ X → (prod witness X ⇒ μ-obj P δ) → prod witness (fobj μ-obj Q (extend δ' X)) ⇒ μ-obj P δ
      step-bwd X x→μ =
        α P δ ∘ fmor P (extend-fam (x→μ ∘ pair to-terminal (id _))) ∘ Iso.bwd (unfold-iso X) ∘ p₂

      fwd : μ-obj P δ ⇒ μ-obj Q δ'
      fwd = ⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)

      bwd : μ-obj Q δ' ⇒ μ-obj P δ
      bwd = ⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)

      iso : Iso (μ-obj P δ) (μ-obj Q δ')
      iso .Iso.fwd = fwd
      iso .Iso.bwd = bwd
      iso .Iso.fwd∘bwd≈id =
        let open ≈-Reasoning isEquiv in begin
            fwd ∘ bwd
          ≈⟨ assoc _ _ _ ⟩
            ⦅ step-fwd ⦆ᴹ ∘ (pair to-terminal (id _) ∘ bwd)
          ≈⟨ ∘-cong₂ (≈-sym (assoc _ _ _)) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ ((pair to-terminal (id _) ∘ ⦅ step-bwd ⦆ᴹ) ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (∘-cong₁ (pair-natural _ _ _)) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ ((pair (to-terminal ∘ ⦅ step-bwd ⦆ᴹ) (id _ ∘ ⦅ step-bwd ⦆ᴹ)) ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (∘-cong₁ (pair-cong (to-terminal-unique _ _) id-left)) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ ((pair to-terminal ⦅ step-bwd ⦆ᴹ) ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (pair-natural _ _ _) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ pair (to-terminal ∘ pair to-terminal (id _)) (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (pair-cong₁ (≈-trans (to-terminal-unique _ _) (≈-sym (pair-p₁ _ _)))) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ pair (p₁ ∘ pair to-terminal (id _)) (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))
          ≈⟨ ∘-cong₂ (≈-sym (pair-natural _ _ _)) ⟩
            ⦅ step-fwd ⦆ᴹ ∘ (pair p₁ ⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
            (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) ∘ pair to-terminal (id _)
          ≈⟨ ∘-cong₁
               (≈-trans (⦅⦆ᴹ-η {P = Q} {δ = δ'} trivial-step (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) fwd∘bwd-β)
                        (strong-μ-fmor-id Q)) ⟩
            p₂ ∘ pair to-terminal (id _)
          ≈⟨ pair-p₂ _ _ ⟩
            id (μ-obj Q δ')
          ∎
        where
          -- The "trivial" Mendler step whose cata is p₂ (by strong-μ-fmor-id).
          trivial-step : ∀ X → (prod witness X ⇒ μ-obj Q δ') →
                         prod witness (fobj μ-obj Q (extend δ' X)) ⇒ μ-obj Q δ'
          trivial-step X x→μ' = α Q δ' ∘ strong-fmor Q (extend-mor (λ _ → p₂) x→μ')

          -- Iso.bwd version of unfold-natural, derived from unfold-natural + iso round-trips.
          unfold-natural-bwd : ∀ {X Y} (f : X ⇒ Y) →
                               (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X)) ≈
                               (Iso.bwd (unfold-iso Y) ∘ fmor Q (extend-fam f))
          unfold-natural-bwd {X} {Y} f = begin
              fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X)
            ≈˘⟨ id-left ⟩
              id _ ∘ (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X))
            ≈˘⟨ ∘-cong₁ (Iso.bwd∘fwd≈id (unfold-iso Y)) ⟩
              (Iso.bwd (unfold-iso Y) ∘ Iso.fwd (unfold-iso Y)) ∘ (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X))
            ≈⟨ assoc _ _ _ ⟩
              Iso.bwd (unfold-iso Y) ∘ (Iso.fwd (unfold-iso Y) ∘ (fmor P (extend-fam f) ∘ Iso.bwd (unfold-iso X)))
            ≈˘⟨ ∘-cong₂ (assoc _ _ _) ⟩
              Iso.bwd (unfold-iso Y) ∘ ((Iso.fwd (unfold-iso Y) ∘ fmor P (extend-fam f)) ∘ Iso.bwd (unfold-iso X))
            ≈˘⟨ ∘-cong₂ (∘-cong₁ (unfold-natural f)) ⟩
              Iso.bwd (unfold-iso Y) ∘ ((fmor Q (extend-fam f) ∘ Iso.fwd (unfold-iso X)) ∘ Iso.bwd (unfold-iso X))
            ≈⟨ ∘-cong₂ (assoc _ _ _) ⟩
              Iso.bwd (unfold-iso Y) ∘ (fmor Q (extend-fam f) ∘ (Iso.fwd (unfold-iso X) ∘ Iso.bwd (unfold-iso X)))
            ≈⟨ ∘-cong₂ (∘-cong₂ (Iso.fwd∘bwd≈id (unfold-iso X))) ⟩
              Iso.bwd (unfold-iso Y) ∘ (fmor Q (extend-fam f) ∘ id _)
            ≈⟨ ∘-cong₂ id-right ⟩
              Iso.bwd (unfold-iso Y) ∘ fmor Q (extend-fam f)
            ∎
            where open ≈-Reasoning isEquiv

          fwd∘bwd-β :
            ((⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) ∘co (α Q δ' ∘ p₂))
            ≈ trivial-step (μ-obj Q δ') (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ)
          fwd∘bwd-β = begin
              (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ) ∘co (α Q δ' ∘ p₂)
            ≈⟨ assoc-co _ _ _ ⟩
              ⦅ step-fwd ⦆ᴹ ∘co (⦅ step-bwd ⦆ᴹ ∘co (α Q δ' ∘ p₂))
            ≈⟨ ∘-cong-co₂ (⦅⦆ᴹ-β {P = Q} {δ = δ'} step-bwd) ⟩
              ⦅ step-fwd ⦆ᴹ ∘co step-bwd (μ-obj Q δ') ⦅ step-bwd ⦆ᴹ
            ≡⟨⟩
              ⦅ step-fwd ⦆ᴹ
                ∘co (α P δ ∘ fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                                    ∘ Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂)
            ≈⟨ ∘-cong-co₂ (assoc _ _ _) ⟩
              ⦅ step-fwd ⦆ᴹ
                ∘co ((α P δ ∘ fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _))))
                     ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂))
            ≈⟨ ∘-cong-co₂ (assoc _ _ _) ⟩
              ⦅ step-fwd ⦆ᴹ
                ∘co (α P δ ∘ (fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                              ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂)))
            ≈⟨ ∘-cong-co₂ (≈-trans (≈-sym (∘-cong₂ (pair-p₂ _ _))) (≈-sym (assoc _ _ _))) ⟩
              ⦅ step-fwd ⦆ᴹ
                ∘co ((α P δ ∘ p₂)
                     ∘co (fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                          ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂)))
            ≈⟨ ≈-sym (assoc-co _ _ _) ⟩
              (⦅ step-fwd ⦆ᴹ ∘co (α P δ ∘ p₂))
                ∘co (fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂))
            ≈⟨ ∘-cong-co₁ (⦅⦆ᴹ-β {P = P} {δ = δ} step-fwd) ⟩
              step-fwd (μ-obj P δ) ⦅ step-fwd ⦆ᴹ
                ∘co (fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ (Iso.bwd (unfold-iso (μ-obj Q δ')) ∘ p₂))
            ≈⟨ ∘-cong-co₂ (≈-sym (assoc _ _ _)) ⟩
              step-fwd (μ-obj P δ) ⦅ step-fwd ⦆ᴹ
                ∘co ((fmor P (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                      ∘ Iso.bwd (unfold-iso (μ-obj Q δ'))) ∘ p₂)
            ≈⟨ ∘-cong-co₂ (∘-cong₁ (unfold-natural-bwd _)) ⟩
              step-fwd (μ-obj P δ) ⦅ step-fwd ⦆ᴹ
                ∘co ((Iso.bwd (unfold-iso (μ-obj P δ))
                      ∘ fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))) ∘ p₂)
            ≡⟨⟩
              (α Q δ' ∘ fmor Q (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)))
                      ∘ Iso.fwd (unfold-iso (μ-obj P δ)) ∘ p₂)
                ∘ pair p₁ ((Iso.bwd (unfold-iso (μ-obj P δ))
                            ∘ fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))) ∘ p₂)
            ≈⟨ ≈-trans (assoc _ _ _) (∘-cong₂ (≈-trans (assoc _ _ _) (∘-cong₂ (≈-trans (assoc _ _ _) (∘-cong₂ (pair-p₂ _ _)))))) ⟩
              α Q δ' ∘ fmor Q (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ Iso.fwd (unfold-iso (μ-obj P δ))
                     ∘ Iso.bwd (unfold-iso (μ-obj P δ))
                     ∘ fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ p₂
            ≈⟨ {!!} ⟩
              α Q δ' ∘ fmor Q (extend-fam (⦅ step-fwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ fmor Q (extend-fam (⦅ step-bwd ⦆ᴹ ∘ pair to-terminal (id _)))
                     ∘ p₂
            ≈⟨ {!!} ⟩
              trivial-step (μ-obj Q δ') (⦅ step-fwd ⦆ᴹ ∘co ⦅ step-bwd ⦆ᴹ)
            ∎
            where open ≈-Reasoning isEquiv

      iso .Iso.bwd∘fwd≈id = {!!}
