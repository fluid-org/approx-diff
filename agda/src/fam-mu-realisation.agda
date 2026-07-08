{-# OPTIONS --prop --postfix-projections --safe #-}

-- Parameterised initial algebras for a category ℰ with setoid-indexed
-- colimits, products, exponentials and strong coproducts, constructed by
-- realising the μ-types of Fam(ℰ). The realised μ-object carries an initial
-- algebra for the realised polynomial endofunctor; the algebra map, fold and
-- laws are established by a mutual induction on polynomials: the collapse
-- isomorphisms (realisation is invariant under replacing an environment entry
-- by a family with isomorphic realisation), initiality via folds transposed
-- through the adjunction between realisation and the singleton embedding, and
-- uniqueness of initial algebras at the inner-μ cases.

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import prop-setoid using (Setoid; module ≈-Reasoning)
open import categories
  using (Category; setoid→category; HasTerminal; HasProducts; HasExponentials;
         HasStrongCoproducts; HasCoproducts; strong-coproducts→coproducts; coKleisli-prod)
open import functor using (Functor; HasColimits)
open import polynomial-functor-2 using (Poly; extend; Poly-map)
import fam
import fam-mu-types-2
import fam-realisation
import polynomial-functor-2
import fam-mu-realisation.natural

module fam-mu-realisation {o m e} (os es : Level) {ℰ : Category o m e}
  (ℰC : ∀ (A : Setoid os (os ⊔ es)) → HasColimits (setoid→category A) ℰ)
  (ℰT : HasTerminal ℰ) (ℰP : HasProducts ℰ) (ℰE : HasExponentials ℰ ℰP)
  (ℰSC : HasStrongCoproducts ℰ ℰP)
  where

open fam-mu-realisation.natural os es ℰC ℰT ℰP ℰE ℰSC public

-- The μ-objects for ℰ itself, via realisation of the Fam(ℰ) μ-objects at
-- singleton-embedded environments.
μ-objℰ : ∀ {n} → Poly ℰ (suc n) → (Fin n → obj) → obj
μ-objℰ P δ = Creal P (λ i → η .fobj (δ i))

private
  module ℰCoprod = HasCoproducts (strong-coproducts→coproducts ℰT ℰSC)

-- The ℰ-interpretation of a polynomial agrees with the realised Fam(ℰ)
-- interpretation, over any pointwise agreement of environments.
fobj-realise-iso : ∀ {n} (P : Poly ℰ n) (δ : Fin n → obj) (δ̂ : Fin n → FM.Obj) →
                   (∀ i → Iso (δ i) (realise .fobj (δ̂ i))) →
                   Iso (ℰI.fobj μ-objℰ P δ) (realise .fobj (FM.fobj FM.μObj (Poly-map η P) δ̂))
fobj-realise-iso (polynomial-functor-2.Poly.const A) δ δ̂ js = Iso-sym (realise-η-iso A)
fobj-realise-iso (polynomial-functor-2.Poly.var i)   δ δ̂ js = js i
fobj-realise-iso (P polynomial-functor-2.Poly.+ Q)   δ δ̂ js =
  Iso-trans
    (ℰCoprod.coproduct-preserve-iso (fobj-realise-iso P δ δ̂ js) (fobj-realise-iso Q δ δ̂ js))
    (Iso-sym (FR.realise-coproducts-iso (strong-coproducts→coproducts ℰT ℰSC) _ _))
fobj-realise-iso (P polynomial-functor-2.Poly.× Q)   δ δ̂ js =
  Iso-trans
    (ℰP.product-preserves-iso (fobj-realise-iso P δ δ̂ js) (fobj-realise-iso Q δ δ̂ js))
    (Iso-sym (FR.realise-products-iso ℰP ℰE _ _))
fobj-realise-iso (polynomial-functor-2.Poly.μ P)     δ δ̂ js =
  MuCollapse.mu-collapse P (collapseAt P) (λ i → η .fobj (δ i)) δ̂
    (λ i → Iso-trans (realise-η-iso (δ i)) (js i))

-- Pointwise agreement between an extended ℰ-environment and its embedded
-- Fam(ℰ) counterpart.
ηjs : ∀ {n} (δ : Fin n → obj) (X : obj) →
      ∀ i → Iso (extend δ X i) (realise .fobj (extend (λ j → η .fobj (δ j)) (η .fobj X) i))
ηjs δ X Fin.zero    = Iso-sym (realise-η-iso X)
ηjs δ X (Fin.suc i) = Iso-sym (realise-η-iso (δ i))

-- The initial-algebra structure for ℰ.
αℰ : ∀ {n} (P : Poly ℰ (suc n)) (δ : Fin n → obj) →
     ℰI.fobj μ-objℰ P (extend δ (μ-objℰ P δ)) ⇒ μ-objℰ P δ
αℰ {n} P δ =
  Initiality.inR P (λ i → η .fobj (δ i)) (collapseAt P) ∘
  fobj-realise-iso P (extend δ (μ-objℰ P δ)) (extend (λ i → η .fobj (δ i)) (η .fobj (μ-objℰ P δ))) (ηjs δ (μ-objℰ P δ)) .Iso.fwd

⦅⦆ℰ : ∀ {n Γ A} {P : Poly ℰ (suc n)} {δ : Fin n → obj} →
      (ℰP.prod Γ (ℰI.fobj μ-objℰ P (extend δ A)) ⇒ A) → ℰP.prod Γ (μ-objℰ P δ) ⇒ A
⦅⦆ℰ {n} {Γ} {A} {P} {δ} alg =
  Initiality.foldR P (λ i → η .fobj (δ i)) (collapseAt P)
    (alg ∘ ℰP.prod-m (id _) (fobj-realise-iso P (extend δ A) (extend (λ i → η .fobj (δ i)) (η .fobj A)) (ηjs δ A) .Iso.bwd))

-- ℰ has Poly-types.
Muℰ : ℰI.HasMu
Muℰ = record { μ-obj = μ-objℰ ; α = αℰ ; ⦅_⦆ = ⦅⦆ℰ }

private
  module ℰMu = ℰI.HasMu Muℰ

-- The realised Fam(ℰ) strong action simulates ℰ's own derived strong action,
-- across the interpretation isomorphism.
SimStmt : ∀ {n} (P : Poly ℰ n) → Prop (o ⊔ m ⊔ e ⊔ Level.suc os ⊔ Level.suc es)
SimStmt {n} P =
  ∀ {Γ : obj} (δ δ' : Fin n → obj) (δ̂ δ̂' : Fin n → FM.Obj)
  (js : ∀ i → Iso (δ i) (realise .fobj (δ̂ i))) (js' : ∀ i → Iso (δ' i) (realise .fobj (δ̂' i)))
  (fs : ∀ i → ℰP.prod Γ (δ i) ⇒ δ' i)
  (ĝs : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂ i)) (δ̂' i)) →
  (∀ i → (fmorη Γ (δ̂ i) (ĝs i) ∘co (js i .Iso.fwd ∘ ℰP.p₂)) ≈ (js' i .Iso.fwd ∘ fs i)) →
  (fmorη Γ (FM.fobj FM.μObj (Poly-map η P) δ̂) (FMu.strong-fmor (Poly-map η P) ĝs)
    ∘co (fobj-realise-iso P δ δ̂ js .Iso.fwd ∘ ℰP.p₂))
  ≈ (fobj-realise-iso P δ' δ̂' js' .Iso.fwd ∘ ℰMu.strong-fmor P fs)

sim-const : ∀ {n} (A : Category.obj ℰ) → SimStmt {n} (polynomial-functor-2.Poly.const A)
sim-const A δ δ' δ̂ δ̂' js js' fs ĝs sqs =
  ≈-trans (CoK.∘-cong₁ (fmorη-p₂ _ _)) CoK.id-left

sim-var : ∀ {n} (i : Fin n) → SimStmt (polynomial-functor-2.Poly.var i)
sim-var i δ δ' δ̂ δ̂' js js' fs ĝs sqs = sqs i

sim-sum : ∀ {n} (P Q : Poly ℰ n) → SimStmt P → SimStmt Q → SimStmt (P polynomial-functor-2.Poly.+ Q)
sim-sum {n} P Q simP simQ {Γ} δ δ' δ̂ δ̂' js js' fs ĝs sqs =
  ≈-trans lhs (≈-sym rhs)
  where
    X̂ : (Fin n → FM.Obj) → FM.Obj
    X̂ γ̂ = FM.fobj FM.μObj (Poly-map η P) γ̂

    Ŷ : (Fin n → FM.Obj) → FM.Obj
    Ŷ γ̂ = FM.fobj FM.μObj (Poly-map η Q) γ̂

    mid : ℰP.prod Γ (ℰCoprod.coprod (ℰI.fobj μ-objℰ P δ) (ℰI.fobj μ-objℰ Q δ)) ⇒ realise .fobj (FCP.coprod (X̂ δ̂') (Ŷ δ̂'))
    mid = ℰSCm.copair
            (realise .fmor FCP.in₁ ∘ (fobj-realise-iso P δ' δ̂' js' .Iso.fwd ∘ ℰMu.strong-fmor P fs))
            (realise .fmor FCP.in₂ ∘ (fobj-realise-iso Q δ' δ̂' js' .Iso.fwd ∘ ℰMu.strong-fmor Q fs))



    lhs : (fmorη Γ (FCP.coprod (X̂ δ̂) (Ŷ δ̂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.+ Q)) ĝs)
            ∘co (fobj-realise-iso (P polynomial-functor-2.Poly.+ Q) δ δ̂ js .Iso.fwd ∘ ℰP.p₂))
          ≈ mid
    lhs =
      begin
        fmorη Γ (FCP.coprod (X̂ δ̂) (Ŷ δ̂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.+ Q)) ĝs)
          ∘co ((K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd)) ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        fmorη Γ (FCP.coprod (X̂ δ̂) (Ŷ δ̂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.+ Q)) ĝs)
          ∘co ((K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ ℰP.p₂) ∘co (ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd) ∘ ℰP.p₂))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (fmorη Γ (FCP.coprod (X̂ δ̂) (Ŷ δ̂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.+ Q)) ĝs)
          ∘co (K⊕ (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ ℰP.p₂)) ∘co (ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (fmorη-scopair Γ (X̂ δ̂) (Ŷ δ̂) _ _) ⟩
        ℰSCm.copair (fmorη Γ (X̂ δ̂) (FM.Mor-∘ FCP.in₁ (FMu.strong-fmor (Poly-map η P) ĝs))) (fmorη Γ (Ŷ δ̂) (FM.Mor-∘ FCP.in₂ (FMu.strong-fmor (Poly-map η Q) ĝs)))
          ∘co (ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd) ∘ ℰP.p₂)
      ≈⟨ scopair-coprod-m _ _ _ _ ⟩
        ℰSCm.copair
          (fmorη Γ (X̂ δ̂) (FM.Mor-∘ FCP.in₁ (FMu.strong-fmor (Poly-map η P) ĝs)) ∘co (fobj-realise-iso P δ δ̂ js .Iso.fwd ∘ ℰP.p₂))
          (fmorη Γ (Ŷ δ̂) (FM.Mor-∘ FCP.in₂ (FMu.strong-fmor (Poly-map η Q) ĝs)) ∘co (fobj-realise-iso Q δ δ̂ js .Iso.fwd ∘ ℰP.p₂))
      ≈⟨ ℰSCm.copair-cong (≈-trans (CoK.∘-cong₁ (fmorη-post Γ (X̂ δ̂) FCP.in₁ _)) (≈-trans (assoc _ _ _) (∘-cong₂ (simP δ δ' δ̂ δ̂' js js' fs ĝs sqs)))) (≈-trans (CoK.∘-cong₁ (fmorη-post Γ (Ŷ δ̂) FCP.in₂ _)) (≈-trans (assoc _ _ _) (∘-cong₂ (simQ δ δ' δ̂ δ̂' js js' fs ĝs sqs)))) ⟩
        mid
      ∎ where open ≈-Reasoning isEquiv



    rhs : (fobj-realise-iso (P polynomial-functor-2.Poly.+ Q) δ' δ̂' js' .Iso.fwd ∘ ℰMu.strong-fmor (P polynomial-functor-2.Poly.+ Q) fs) ≈ mid
    rhs =
      ≈-trans (ℰSCm.copair-natural _ _ _)
        (ℰSCm.copair-cong
          (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (ℰCoprod.copair-in₁ _ _)) (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (K⊕-in₁ (X̂ δ̂') (Ŷ δ̂'))))))) (assoc _ _ _)))
          (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (ℰCoprod.copair-in₂ _ _)) (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ (K⊕-in₂ (X̂ δ̂') (Ŷ δ̂'))))))) (assoc _ _ _))))

sim-prod : ∀ {n} (P Q : Poly ℰ n) → SimStmt P → SimStmt Q → SimStmt (P polynomial-functor-2.Poly.× Q)
sim-prod {n} P Q simP simQ {Γ} δ δ' δ̂ δ̂' js js' fs ĝs sqs =
  ≈-trans lhs (≈-sym rhs)
  where
    X̂ : (Fin n → FM.Obj) → FM.Obj
    X̂ γ̂ = FM.fobj FM.μObj (Poly-map η P) γ̂

    Ŷ : (Fin n → FM.Obj) → FM.Obj
    Ŷ γ̂ = FM.fobj FM.μObj (Poly-map η Q) γ̂

    mid : ℰP.prod Γ (ℰP.prod (ℰI.fobj μ-objℰ P δ) (ℰI.fobj μ-objℰ Q δ)) ⇒ realise .fobj (FM.Fam𝒞-P.prod (X̂ δ̂') (Ŷ δ̂'))
    mid = K× (X̂ δ̂') (Ŷ δ̂') .Iso.bwd ∘
          ℰP.strong-prod-m
            (fobj-realise-iso P δ' δ̂' js' .Iso.fwd ∘ ℰMu.strong-fmor P fs)
            (fobj-realise-iso Q δ' δ̂' js' .Iso.fwd ∘ ℰMu.strong-fmor Q fs)



    lhs : (fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂) (Ŷ δ̂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.× Q)) ĝs)
            ∘co (fobj-realise-iso (P polynomial-functor-2.Poly.× Q) δ δ̂ js .Iso.fwd ∘ ℰP.p₂))
          ≈ mid
    lhs =
      begin
        fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂) (Ŷ δ̂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.× Q)) ĝs)
          ∘co ((K× (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd)) ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₂ (co-pure _ _) ⟩
        fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂) (Ŷ δ̂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.× Q)) ĝs)
          ∘co ((K× (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ ℰP.p₂) ∘co (ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd) ∘ ℰP.p₂))
      ≈˘⟨ CoK.assoc _ _ _ ⟩
        (fmorη Γ (FM.Fam𝒞-P.prod (X̂ δ̂) (Ŷ δ̂)) (FMu.strong-fmor (Poly-map η (P polynomial-functor-2.Poly.× Q)) ĝs)
          ∘co (K× (X̂ δ̂) (Ŷ δ̂) .Iso.bwd ∘ ℰP.p₂)) ∘co (ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd) ∘ ℰP.p₂)
      ≈⟨ CoK.∘-cong₁ (fmorη-sprodm Γ (X̂ δ̂) (Ŷ δ̂) _ _) ⟩
        (K× (X̂ δ̂') (Ŷ δ̂') .Iso.bwd ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂) (FMu.strong-fmor (Poly-map η P) ĝs)) (fmorη Γ (Ŷ δ̂) (FMu.strong-fmor (Poly-map η Q) ĝs)))
          ∘co (ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd) ∘ ℰP.p₂)
      ≈⟨ assoc _ _ _ ⟩
        K× (X̂ δ̂') (Ŷ δ̂') .Iso.bwd ∘ (ℰP.strong-prod-m (fmorη Γ (X̂ δ̂) (FMu.strong-fmor (Poly-map η P) ĝs)) (fmorη Γ (Ŷ δ̂) (FMu.strong-fmor (Poly-map η Q) ĝs)) ∘co (ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd) ∘ ℰP.p₂))
      ≈⟨ ∘-cong₂ (∘-cong₂ (ℰP.pair-cong (≈-sym id-left) ≈-refl)) ⟩
        K× (X̂ δ̂') (Ŷ δ̂') .Iso.bwd ∘ (ℰP.strong-prod-m (fmorη Γ (X̂ δ̂) (FMu.strong-fmor (Poly-map η P) ĝs)) (fmorη Γ (Ŷ δ̂) (FMu.strong-fmor (Poly-map η Q) ĝs)) ∘ ℰP.prod-m (id _) (ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd)))
      ≈⟨ ∘-cong₂ (ℰP.strong-prod-m-pre _ _ _ _ _) ⟩
        K× (X̂ δ̂') (Ŷ δ̂') .Iso.bwd ∘ ℰP.strong-prod-m (fmorη Γ (X̂ δ̂) (FMu.strong-fmor (Poly-map η P) ĝs) ∘ ℰP.prod-m (id _) (fobj-realise-iso P δ δ̂ js .Iso.fwd)) (fmorη Γ (Ŷ δ̂) (FMu.strong-fmor (Poly-map η Q) ĝs) ∘ ℰP.prod-m (id _) (fobj-realise-iso Q δ δ̂ js .Iso.fwd))
      ≈⟨ ∘-cong₂ (ℰP.strong-prod-m-cong (≈-trans (∘-cong₂ (ℰP.pair-cong id-left ≈-refl)) (simP δ δ' δ̂ δ̂' js js' fs ĝs sqs)) (≈-trans (∘-cong₂ (ℰP.pair-cong id-left ≈-refl)) (simQ δ δ' δ̂ δ̂' js js' fs ĝs sqs))) ⟩
        mid
      ∎ where open ≈-Reasoning isEquiv

    rhs : (fobj-realise-iso (P polynomial-functor-2.Poly.× Q) δ' δ̂' js' .Iso.fwd ∘ ℰMu.strong-fmor (P polynomial-functor-2.Poly.× Q) fs) ≈ mid
    rhs =
      ≈-trans (assoc _ _ _)
        (∘-cong₂ (ℰP.strong-prod-m-post _ _ _ _))

-- The interpretation isomorphism respects pointwise-equal agreements.
SI-ext : ∀ {n} (P : Poly ℰ n) (δ : Fin n → obj) (δ̂ : Fin n → FM.Obj)
         (js js' : ∀ i → Iso (δ i) (realise .fobj (δ̂ i))) →
         (∀ i → js i .Iso.fwd ≈ js' i .Iso.fwd) →
         fobj-realise-iso P δ δ̂ js .Iso.fwd ≈ fobj-realise-iso P δ δ̂ js' .Iso.fwd
SI-ext (polynomial-functor-2.Poly.const A) δ δ̂ js js' hyps = ≈-refl
SI-ext (polynomial-functor-2.Poly.var i)   δ δ̂ js js' hyps = hyps i
SI-ext (P polynomial-functor-2.Poly.+ Q)   δ δ̂ js js' hyps =
  ∘-cong₂ (ℰCoprod.coprod-m-cong (SI-ext P δ δ̂ js js' hyps) (SI-ext Q δ δ̂ js js' hyps))
SI-ext (P polynomial-functor-2.Poly.× Q)   δ δ̂ js js' hyps =
  ∘-cong₂ (ℰP.prod-m-cong (SI-ext P δ δ̂ js js' hyps) (SI-ext Q δ δ̂ js js' hyps))
SI-ext (polynomial-functor-2.Poly.μ P)     δ δ̂ js js' hyps =
  collapse-ext (polynomial-functor-2.Poly.μ P) (collapseAt (polynomial-functor-2.Poly.μ P)) _ _ _ _
    (λ i → ∘-cong₁ (hyps i))

-- A collapse after the interpretation isomorphism fuses into the agreement.
SI-collapse : ∀ {n} (P : Poly ℰ n) (δ : Fin n → obj) (δ̂ δ̂'' : Fin n → FM.Obj)
              (js : ∀ i → Iso (δ i) (realise .fobj (δ̂ i)))
              (isos : ∀ i → Iso (realise .fobj (δ̂ i)) (realise .fobj (δ̂'' i))) →
              (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd ∘ fobj-realise-iso P δ δ̂ js .Iso.fwd)
              ≈ fobj-realise-iso P δ δ̂'' (λ i → Iso-trans (js i) (isos i)) .Iso.fwd
SI-collapse (polynomial-functor-2.Poly.const A) δ δ̂ δ̂'' js isos = id-left
SI-collapse (polynomial-functor-2.Poly.var i)   δ δ̂ δ̂'' js isos = ≈-refl
SI-collapse (P polynomial-functor-2.Poly.+ Q)   δ δ̂ δ̂'' js isos =
  begin
    ((K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰCoprod.coprod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd)) ∘ K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.fwd) ∘ (K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.bwd ∘ ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd))
  ≈⟨ assoc _ _ _ ⟩
    (K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰCoprod.coprod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd)) ∘ (K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.fwd ∘ (K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.bwd ∘ ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd)))
  ≈⟨ ∘-cong₂ (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.fwd∘bwd≈id)) id-left)) ⟩
    (K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰCoprod.coprod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd)) ∘ ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd)
  ≈⟨ assoc _ _ _ ⟩
    K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ (ℰCoprod.coprod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) ∘ ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd))
  ≈˘⟨ ∘-cong₂ (ℰCoprod.coprod-m-comp _ _ _ _) ⟩
    K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰCoprod.coprod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd ∘ fobj-realise-iso P δ δ̂ js .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd ∘ fobj-realise-iso Q δ δ̂ js .Iso.fwd)
  ≈⟨ ∘-cong₂ (ℰCoprod.coprod-m-cong (SI-collapse P δ δ̂ δ̂'' js isos) (SI-collapse Q δ δ̂ δ̂'' js isos)) ⟩
    K⊕ (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰCoprod.coprod-m (fobj-realise-iso P δ δ̂'' (λ i → Iso-trans (js i) (isos i)) .Iso.fwd) (fobj-realise-iso Q δ δ̂'' (λ i → Iso-trans (js i) (isos i)) .Iso.fwd)
  ∎ where open ≈-Reasoning isEquiv
SI-collapse (P polynomial-functor-2.Poly.× Q)   δ δ̂ δ̂'' js isos =
  begin
    ((K× (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰP.prod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd)) ∘ K× (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.fwd) ∘ (K× (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.bwd ∘ ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd))
  ≈⟨ assoc _ _ _ ⟩
    (K× (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰP.prod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd)) ∘ (K× (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.fwd ∘ (K× (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.bwd ∘ ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd)))
  ≈⟨ ∘-cong₂ (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong₁ (K× (FM.fobj FM.μObj (Poly-map η P) δ̂) (FM.fobj FM.μObj (Poly-map η Q) δ̂) .Iso.fwd∘bwd≈id)) id-left)) ⟩
    (K× (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰP.prod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd)) ∘ ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd)
  ≈⟨ assoc _ _ _ ⟩
    K× (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ (ℰP.prod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd) ∘ ℰP.prod-m (fobj-realise-iso P δ δ̂ js .Iso.fwd) (fobj-realise-iso Q δ δ̂ js .Iso.fwd))
  ≈˘⟨ ∘-cong₂ (ℰP.prod-m-comp _ _ _ _) ⟩
    K× (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰP.prod-m (collapseAt P .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd ∘ fobj-realise-iso P δ δ̂ js .Iso.fwd) (collapseAt Q .CollapseAt.iso δ̂ δ̂'' isos .Iso.fwd ∘ fobj-realise-iso Q δ δ̂ js .Iso.fwd)
  ≈⟨ ∘-cong₂ (ℰP.prod-m-cong (SI-collapse P δ δ̂ δ̂'' js isos) (SI-collapse Q δ δ̂ δ̂'' js isos)) ⟩
    K× (FM.fobj FM.μObj (Poly-map η P) δ̂'') (FM.fobj FM.μObj (Poly-map η Q) δ̂'') .Iso.bwd ∘ ℰP.prod-m (fobj-realise-iso P δ δ̂'' (λ i → Iso-trans (js i) (isos i)) .Iso.fwd) (fobj-realise-iso Q δ δ̂'' (λ i → Iso-trans (js i) (isos i)) .Iso.fwd)
  ∎ where open ≈-Reasoning isEquiv
SI-collapse (polynomial-functor-2.Poly.μ P)     δ δ̂ δ̂'' js isos =
  ≈-trans (≈-sym (mu-collapse-comp P (collapseAt P) _ δ̂ δ̂'' _ isos))
    (collapse-ext-μ)
  where
    collapse-ext-μ : MuCollapse.mu-collapse P (collapseAt P) (λ i → η .fobj (δ i)) δ̂'' (λ i → Iso-trans (Iso-trans (realise-η-iso (δ i)) (js i)) (isos i)) .Iso.fwd
                     ≈ MuCollapse.mu-collapse P (collapseAt P) (λ i → η .fobj (δ i)) δ̂'' (λ i → Iso-trans (realise-η-iso (δ i)) (Iso-trans (js i) (isos i))) .Iso.fwd
    collapse-ext-μ = collapse-ext (polynomial-functor-2.Poly.μ P) (collapseAt (polynomial-functor-2.Poly.μ P)) _ _ _ _
      (λ i → ≈-sym (assoc _ _ _))

sim-mu : ∀ {n} (P : Poly ℰ (suc n)) → SimStmt P → SimStmt (polynomial-functor-2.Poly.μ P)
sim-mu {n} P simP {Γ} δ δ' δ̂ δ̂' js js' fs ĝs sqs =
  ≈-trans step1 (∘-cong₂ μ-key)
  where
    Q̂ = Poly-map η P
    CP = collapseAt P

    δ̂η δ̂η' : Fin n → FM.Obj
    δ̂η  i = η .fobj (δ i)
    δ̂η' i = η .fobj (δ' i)

    μℰ' = μ-objℰ P δ'
    μ̂' = FM.μObj Q̂ δ̂η'

    ctfs : ∀ i → FM.Mor (FM.Fam𝒞-P.prod (η .fobj Γ) (δ̂η i)) (δ̂η' i)
    ctfs i = ctxη Γ (δ i) (fs i)

    module Mδ = Initiality P δ̂η CP
    module M' = Initiality P δ̂η' CP
    module Sd = SμfFold P CP δ̂η δ̂η' ctfs

    sqs' : ∀ i → (fmorη Γ (δ̂ i) (ĝs i) ∘co (Iso-trans (realise-η-iso (δ i)) (js i) .Iso.fwd ∘ ℰP.p₂))
                 ≈ (Iso-trans (realise-η-iso (δ' i)) (js' i) .Iso.fwd ∘ fmorη Γ (δ̂η i) (ctfs i))
    sqs' i =
      ≈-trans (CoK.∘-cong₂ (≈-sym (co-pure _ _)))
        (≈-trans (≈-sym (CoK.assoc _ _ _))
          (≈-trans (CoK.∘-cong₁ (sqs i))
            (≈-trans (assoc _ _ _)
              (≈-trans (∘-cong₂ (∘-cong₂ (ℰP.pair-cong (≈-sym id-left) ≈-refl)))
                (≈-sym (≈-trans (assoc _ _ _) (∘-cong₂ (ctxη-counit Γ (δ i) (fs i)))))))))

    step1 : (fmorη Γ (FM.μObj Q̂ δ̂) (FMu.strong-μ-fmor Q̂ ĝs)
              ∘co (fobj-realise-iso (polynomial-functor-2.Poly.μ P) δ δ̂ js .Iso.fwd ∘ ℰP.p₂))
            ≈ (fobj-realise-iso (polynomial-functor-2.Poly.μ P) δ' δ̂' js' .Iso.fwd ∘ fmorη Γ (FM.μObj Q̂ δ̂η) (FMu.strong-μ-fmor Q̂ ctfs))
    step1 =
      MuNat.mu-natural P CP δ̂η δ̂ δ̂η' δ̂'
        (λ i → Iso-trans (realise-η-iso (δ i)) (js i))
        (λ i → Iso-trans (realise-η-iso (δ' i)) (js' i))
        ctfs ĝs sqs'

    jsE : ∀ i → Iso (extend δ μℰ' i) (realise .fobj (extend δ̂η μ̂' i))
    jsE Fin.zero    = Iso-refl
    jsE (Fin.suc i) = Iso-sym (realise-η-iso (δ i))

    jsE' : ∀ i → Iso (extend δ' μℰ' i) (realise .fobj (extend δ̂η' μ̂' i))
    jsE' Fin.zero    = Iso-refl
    jsE' (Fin.suc i) = Iso-sym (realise-η-iso (δ' i))

    SIA = fobj-realise-iso P (extend δ μℰ') (extend δ̂η (η .fobj μℰ')) (ηjs δ μℰ')
    SIμext = fobj-realise-iso P (extend δ' μℰ') (extend δ̂η' (η .fobj μℰ')) (ηjs δ' μℰ')
    SIE = fobj-realise-iso P (extend δ μℰ') (extend δ̂η μ̂') jsE
    SIE' = fobj-realise-iso P (extend δ' μℰ') (extend δ̂η' μ̂') jsE'

    sfF = FMu.strong-fmor Q̂ (FMu.strong-extend-mor ctfs FM.Fam𝒞-P.p₂)

    sqsE : ∀ i → (fmorη Γ (extend δ̂η μ̂' i) (FMu.strong-extend-mor ctfs FM.Fam𝒞-P.p₂ i) ∘co (jsE i .Iso.fwd ∘ ℰP.p₂))
                 ≈ (jsE' i .Iso.fwd ∘ ℰMu.strong-extend-mor fs ℰP.p₂ i)
    sqsE Fin.zero    = ≈-trans (CoK.∘-cong₁ (fmorη-p₂ Γ μ̂')) CoK.id-left
    sqsE (Fin.suc i) = ctxη-counit-sq Γ (δ i) (fs i)

    ihE : (fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂η μ̂')) sfF ∘co (SIE .Iso.fwd ∘ ℰP.p₂))
          ≈ (SIE' .Iso.fwd ∘ ℰMu.strong-fmor P (ℰMu.strong-extend-mor fs ℰP.p₂))
    ihE = simP (extend δ μℰ') (extend δ' μℰ') (extend δ̂η μ̂') (extend δ̂η' μ̂') jsE jsE'
            (ℰMu.strong-extend-mor fs ℰP.p₂) (FMu.strong-extend-mor ctfs FM.Fam𝒞-P.p₂) sqsE

    fuseA : (Sd.KKε .Iso.fwd ∘ SIA .Iso.fwd) ≈ SIE .Iso.fwd
    fuseA =
      ≈-trans (SI-collapse P (extend δ μℰ') (extend δ̂η (η .fobj μℰ')) (extend δ̂η μ̂') (ηjs δ μℰ') Sd.KKisos)
        (SI-ext P (extend δ μℰ') (extend δ̂η μ̂') _ jsE pw)
      where
        pw : ∀ i → Iso-trans (ηjs δ μℰ' i) (Sd.KKisos i) .Iso.fwd ≈ jsE i .Iso.fwd
        pw Fin.zero    = realise-η-iso μℰ' .Iso.fwd∘bwd≈id
        pw (Fin.suc i) = id-left

    fuseM : (CP .CollapseAt.iso (extend δ̂η' (η .fobj (Creal P δ̂η'))) (extend δ̂η' μ̂') M'.inIsos .Iso.fwd ∘ SIμext .Iso.fwd) ≈ SIE' .Iso.fwd
    fuseM =
      ≈-trans (SI-collapse P (extend δ' μℰ') (extend δ̂η' (η .fobj μℰ')) (extend δ̂η' μ̂') (ηjs δ' μℰ') M'.inIsos)
        (SI-ext P (extend δ' μℰ') (extend δ̂η' μ̂') _ jsE' pw)
      where
        pw : ∀ i → Iso-trans (ηjs δ' μℰ' i) (M'.inIsos i) .Iso.fwd ≈ jsE' i .Iso.fwd
        pw Fin.zero    = realise-η-iso μℰ' .Iso.fwd∘bwd≈id
        pw (Fin.suc i) = id-left

    inR-decomp : (M'.inR ∘ SIμext .Iso.fwd) ≈ (realise .fmor (FMu.α Q̂ δ̂η') ∘ SIE' .Iso.fwd)
    inR-decomp =
      ≈-trans (∘-cong₁ inRK') (≈-trans (assoc _ _ _) (∘-cong₂ fuseM))
      where
        inRK' : M'.inR ≈ (realise .fmor (FMu.α Q̂ δ̂η') ∘ CP .CollapseAt.iso (extend δ̂η' (η .fobj (Creal P δ̂η'))) (extend δ̂η' μ̂') M'.inIsos .Iso.fwd)
        inRK' =
          ≈-sym (≈-trans (∘-cong₁ (inR-K P δ̂η' CP))
            (≈-trans (assoc _ _ _)
              (≈-trans (∘-cong₂ (CP .CollapseAt.iso _ _ M'.inIsos .Iso.bwd∘fwd≈id)) id-right)))

    cancelSIE : (SIE .Iso.fwd ∘ SIA .Iso.bwd) ≈ Sd.KKε .Iso.fwd
    cancelSIE =
      ≈-trans (∘-cong₁ (≈-sym fuseA))
        (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (SIA .Iso.fwd∘bwd≈id)) id-right))

    C : ((αℰ P δ' ∘ ℰMu.strong-fmor P (ℰMu.strong-extend-mor fs ℰP.p₂)) ∘ ℰP.prod-m (id _) (SIA .Iso.bwd)) ≈ Sd.aStar
    C =
      begin
        ((M'.inR ∘ SIμext .Iso.fwd) ∘ ℰMu.strong-fmor P (ℰMu.strong-extend-mor fs ℰP.p₂)) ∘ ℰP.prod-m (id _) (SIA .Iso.bwd)
      ≈⟨ ∘-cong₁ (∘-cong₁ inR-decomp) ⟩
        ((realise .fmor (FMu.α Q̂ δ̂η') ∘ SIE' .Iso.fwd) ∘ ℰMu.strong-fmor P (ℰMu.strong-extend-mor fs ℰP.p₂)) ∘ ℰP.prod-m (id _) (SIA .Iso.bwd)
      ≈⟨ ∘-cong₁ (assoc _ _ _) ⟩
        (realise .fmor (FMu.α Q̂ δ̂η') ∘ (SIE' .Iso.fwd ∘ ℰMu.strong-fmor P (ℰMu.strong-extend-mor fs ℰP.p₂))) ∘ ℰP.prod-m (id _) (SIA .Iso.bwd)
      ≈˘⟨ ∘-cong₁ (∘-cong₂ ihE) ⟩
        (realise .fmor (FMu.α Q̂ δ̂η') ∘ (fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂η μ̂')) sfF ∘co (SIE .Iso.fwd ∘ ℰP.p₂))) ∘ ℰP.prod-m (id _) (SIA .Iso.bwd)
      ≈˘⟨ ∘-cong₁ (assoc _ _ _) ⟩
        ((realise .fmor (FMu.α Q̂ δ̂η') ∘ fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂η μ̂')) sfF) ∘co (SIE .Iso.fwd ∘ ℰP.p₂)) ∘ ℰP.prod-m (id _) (SIA .Iso.bwd)
      ≈⟨ assoc _ _ _ ⟩
        (realise .fmor (FMu.α Q̂ δ̂η') ∘ fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂η μ̂')) sfF) ∘ (ℰP.pair ℰP.p₁ (SIE .Iso.fwd ∘ ℰP.p₂) ∘ ℰP.prod-m (id _) (SIA .Iso.bwd))
      ≈⟨ ∘-cong₂ (ℰP.pair-natural _ _ _) ⟩
        (realise .fmor (FMu.α Q̂ δ̂η') ∘ fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂η μ̂')) sfF) ∘ ℰP.pair (ℰP.p₁ ∘ ℰP.prod-m (id _) (SIA .Iso.bwd)) ((SIE .Iso.fwd ∘ ℰP.p₂) ∘ ℰP.prod-m (id _) (SIA .Iso.bwd))
      ≈⟨ ∘-cong₂ (ℰP.pair-cong (≈-trans (ℰP.pair-p₁ _ _) id-left) (≈-trans (assoc _ _ _) (≈-trans (∘-cong₂ (ℰP.pair-p₂ _ _)) (≈-trans (≈-sym (assoc _ _ _)) (∘-cong₁ cancelSIE))))) ⟩
        (realise .fmor (FMu.α Q̂ δ̂η') ∘ fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂η μ̂')) sfF) ∘co (Sd.KKε .Iso.fwd ∘ ℰP.p₂)
      ≈˘⟨ CoK.∘-cong₁ (fmorη-post Γ (FM.fobj FM.μObj Q̂ (extend δ̂η μ̂')) (FMu.α Q̂ δ̂η') sfF) ⟩
        fmorη Γ (FM.fobj FM.μObj Q̂ (extend δ̂η μ̂')) (FM.Mor-∘ (FMu.α Q̂ δ̂η') sfF) ∘co (Sd.KKε .Iso.fwd ∘ ℰP.p₂)
      ∎
      where
        open ≈-Reasoning isEquiv



    μ-key : fmorη Γ (FM.μObj Q̂ δ̂η) (FMu.strong-μ-fmor Q̂ ctfs) ≈ ℰMu.strong-fmor (polynomial-functor-2.Poly.μ P) fs
    μ-key = ≈-trans Sd.sμf-fold (Mδ.foldR-cong (≈-sym C))

-- The simulation, tied over all polynomials.
sim : ∀ {n} (P : Poly ℰ n) → SimStmt P
sim (polynomial-functor-2.Poly.const A) = sim-const A
sim (polynomial-functor-2.Poly.var i)   = sim-var i
sim (P polynomial-functor-2.Poly.+ Q)   = sim-sum P Q (sim P) (sim Q)
sim (P polynomial-functor-2.Poly.× Q)   = sim-prod P Q (sim P) (sim Q)
sim (polynomial-functor-2.Poly.μ P)     = sim-mu P (sim P)
