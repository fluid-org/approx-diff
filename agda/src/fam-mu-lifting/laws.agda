{-# OPTIONS --prop --postfix-projections --safe #-}

-- The initial-algebra laws for the μ-types, stated against one application of the algebra to a
-- candidate at the recursive positions, by the same recursion as the fold: the fold is such an
-- application of the algebra to itself, and is the only morphism that is.

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import prop-setoid as PS using ()
open import indexed-family using (_⇒f_)
import fam-mu-lifting.lambek

module fam-mu-lifting.laws {o m e} (os es : Level) {𝒞 : Category o m e}
    (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙c : Category.obj 𝒞) where

open fam-mu-lifting.lambek os es CM BP 𝟙c public

private module CME = CMonEnriched CM
open CME using (_+m_)

-- One application of the algebra against a candidate at the recursive positions: the same
-- recursion as the fold, with the candidate at the slot.
module ApplyDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (let module Tδ = Tree δ)
    (h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier)
    (h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
              _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t'))
    (h-fam : ∀ γ t →
             prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t))
    where
    open FoldBase {n} {Γ} {A} {P} {δ} hiding (module Tδ)
    mutual
      apply-shape-idx : (Q : Poly (suc n)) → Γ .idx .Carrier → Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣) →
                      fobj μ-fam Q (extend δ A) .idx .Carrier
      apply-shape-idx (const A')        γ a = a
      apply-shape-idx (var Fin.zero)    γ t = h-idx γ t
      apply-shape-idx (var (Fin.suc i)) γ a = a
      apply-shape-idx (Q₁ + Q₂) γ (inj₁ x) = inj₁ (apply-shape-idx Q₁ γ x)
      apply-shape-idx (Q₁ + Q₂) γ (inj₂ y) = inj₂ (apply-shape-idx Q₂ γ y)
      apply-shape-idx (Q₁ × Q₂) γ (x , y) = apply-shape-idx Q₁ γ x , apply-shape-idx Q₂ γ y
      apply-shape-idx (μ Q')    γ t = apply-reindex {Q = Q'} γ fbase t

      apply-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') →
                     Tδ.W ∣ Q ∣ ρ → TA'.W ∣ Q ∣ ρ'
      apply-reindex {Q = Q} γ fm (Tδ.sup x) = TA'.sup (apply-reindex-shape γ Q (fbind Q fm) x)

      apply-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB) →
                           Tδ.⟦ ∣ R ∣ ⟧shape ηA → TA'.⟦ ∣ R ∣ ⟧shape ηB
      apply-reindex-shape γ (const A') fm a = a
      apply-reindex-shape γ (var v)    fm a = apply-apply γ fm v a
      apply-reindex-shape γ (P' + Q') fm (inj₁ a) = inj₁ (apply-reindex-shape γ P' fm a)
      apply-reindex-shape γ (P' + Q') fm (inj₂ b) = inj₂ (apply-reindex-shape γ Q' fm b)
      apply-reindex-shape γ (P' × Q') fm (a , b) = apply-reindex-shape γ P' fm a , apply-reindex-shape γ Q' fm b
      apply-reindex-shape γ (μ Q'')   fm t = apply-reindex {Q = Q''} γ fm t

      apply-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k) →
                   Tδ.El (ρ v) → TA'.El (ρ' v)
      apply-apply γ fbase        Fin.zero    t = h-idx γ t
      apply-apply γ fbase        (Fin.suc i) a = a
      apply-apply γ (fbind Q fm) Fin.zero    a = apply-reindex {Q = Q} γ fm a
      apply-apply γ (fbind Q fm) (Fin.suc v) a = apply-apply γ fm v a

    mutual
      apply-shape-idx-resp : (Q : Poly (suc n)) → ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {x x'}
                           (p : Tδ.shape≈ ∣ Q ∣ (Srt.η₀ ∣ P ∣) x x') →
                           _≈s_ (fobj μ-fam Q (extend δ A) .idx) (apply-shape-idx Q γ x) (apply-shape-idx Q γ' x')
      apply-shape-idx-resp (const A')        γ≈ p = p
      apply-shape-idx-resp (var Fin.zero)    γ≈ {x} {x'} p = h-resp γ≈ {x} {x'} p
      apply-shape-idx-resp (var (Fin.suc i)) γ≈ p = p
      apply-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} p = apply-shape-idx-resp Q₁ γ≈ p
      apply-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} p = apply-shape-idx-resp Q₂ γ≈ p
      apply-shape-idx-resp (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (p₁ , p₂) =
        apply-shape-idx-resp Q₁ γ≈ p₁ , apply-shape-idx-resp Q₂ γ≈ p₂
      apply-shape-idx-resp (μ Q')    γ≈ {x} {x'} p = apply-reindex-resp {Q = Q'} γ≈ fbase {x} {x'} p

      apply-reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d')
                          {t t' : Tδ.W ∣ Q ∣ ρ} (p : Tδ.W-≈ t t') →
                          TA'.W-≈ (apply-reindex γ fm t) (apply-reindex γ' fm t')
      apply-reindex-resp {Q = Q} γ≈ fm {Tδ.sup x} {Tδ.sup y} p = apply-reindex-shape-resp γ≈ Q (fbind Q fm) {x} {y} p

      apply-reindex-shape-resp : ∀ {j} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                                {a a' : Tδ.⟦ ∣ R ∣ ⟧shape ηA} (p : Tδ.shape≈ ∣ R ∣ ηA a a') →
                                TA'.shape≈ ∣ R ∣ ηB (apply-reindex-shape γ R fm a) (apply-reindex-shape γ' R fm a')
      apply-reindex-shape-resp γ≈ (const A') fm p = p
      apply-reindex-shape-resp γ≈ (var v)    fm p = apply-apply-resp γ≈ fm v p
      apply-reindex-shape-resp γ≈ (P' + Q') fm {inj₁ _} {inj₁ _} p = apply-reindex-shape-resp γ≈ P' fm p
      apply-reindex-shape-resp γ≈ (P' + Q') fm {inj₂ _} {inj₂ _} p = apply-reindex-shape-resp γ≈ Q' fm p
      apply-reindex-shape-resp γ≈ (P' × Q') fm {_ , _} {_ , _} (p₁ , p₂) =
        apply-reindex-shape-resp γ≈ P' fm p₁ , apply-reindex-shape-resp γ≈ Q' fm p₂
      apply-reindex-shape-resp γ≈ (μ Q'')   fm {a} {a'} p = apply-reindex-resp {Q = Q''} γ≈ fm {a} {a'} p

      apply-apply-resp : ∀ {k} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d') (v : Fin k)
                        {a a'} (p : Tδ.elEq (ρ v) a a') →
                        TA'.elEq (ρ' v) (apply-apply γ fm v a) (apply-apply γ' fm v a')
      apply-apply-resp γ≈ fbase        Fin.zero    {a} {a'} p = h-resp γ≈ {a} {a'} p
      apply-apply-resp γ≈ fbase        (Fin.suc i) p = p
      apply-apply-resp γ≈ (fbind Q fm) Fin.zero    {a} {a'} p = apply-reindex-resp {Q = Q} γ≈ fm {a} {a'} p
      apply-apply-resp γ≈ (fbind Q fm) (Fin.suc v) p = apply-apply-resp γ≈ fm v p

    mutual
      apply-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                       prod (Γ .fam .fm γ) (Tδ.fib-shape Q (Tδ.deco-ext P (λ i → lift tt)) x)
                         ⇒ fobj μ-fam Q (extend δ A) .fam .fm (apply-shape-idx Q γ x)
      apply-shape-fam (const A')        γ a = p₂
      apply-shape-fam (var Fin.zero)    γ t = h-fam γ t
      apply-shape-fam (var (Fin.suc i)) γ a = p₂
      apply-shape-fam (Q₁ + Q₂) γ (inj₁ x) = under-root (apply-shape-fam Q₁ γ x)
      apply-shape-fam (Q₁ + Q₂) γ (inj₂ y) = under-root (apply-shape-fam Q₂ γ y)
      apply-shape-fam (Q₁ × Q₂) γ (x , y) =
        under-root (strong-prod-m (apply-shape-fam Q₁ γ x) (apply-shape-fam Q₂ γ y))
      apply-shape-fam (μ Q')    γ t = apply-reindex-fam {Q = Q'} γ fbase t

      apply-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                         prod (Γ .fam .fm γ) (Tδ.fib Q d t) ⇒ TA'.fib Q d' (apply-reindex γ md t)
      apply-reindex-fam {Q = Q} γ md (Tδ.sup x) = apply-reindex-shape-fam γ Q (fbind Q md) x

      apply-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                               prod (Γ .fam .fm γ) (Tδ.fib-shape R dA a) ⇒ TA'.fib-shape R dB (apply-reindex-shape γ R md a)
      apply-reindex-shape-fam γ (const A') md a = p₂
      apply-reindex-shape-fam γ (var v)    md a = apply-apply-fam γ md v a
      apply-reindex-shape-fam γ (P' + Q') md (inj₁ a) = under-root (apply-reindex-shape-fam γ P' md a)
      apply-reindex-shape-fam γ (P' + Q') md (inj₂ b) = under-root (apply-reindex-shape-fam γ Q' md b)
      apply-reindex-shape-fam γ (P' × Q') md (a , b) =
        under-root (strong-prod-m (apply-reindex-shape-fam γ P' md a) (apply-reindex-shape-fam γ Q' md b))
      apply-reindex-shape-fam γ (μ Q'')   md t = apply-reindex-fam {Q = Q''} γ md t

      apply-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (v : Fin k) (a : Tδ.El (ρ v)) →
                       prod (Γ .fam .fm γ) (Tδ.fib-el (ρ v) (d v) a) ⇒ TA'.fib-el (ρ' v) (d' v) (apply-apply γ md v a)
      apply-apply-fam γ fbase        Fin.zero    t = h-fam γ t
      apply-apply-fam γ fbase        (Fin.suc i) a = p₂
      apply-apply-fam γ (fbind Q md) Fin.zero    a = apply-reindex-fam {Q = Q} γ md a
      apply-apply-fam γ (fbind Q md) (Fin.suc v) a = apply-apply-fam γ md v a


-- The fused law and its β half: the fold is the algebra applied to itself, the agreement between
-- the fold's recursion and the candidate application at the fold being a congruence, since the
-- candidate slot is the fold on the nose.
module Laws {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
  open FoldBase {n} {Γ} {A} {P} {δ}
  module Ft = FoldDef {n} {Γ} {A} {P} {δ} alg
  module Ap (h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier)
            (h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                      _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t'))
            (h-fam : ∀ γ t →
                     prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t)) =
    ApplyDef {n} {Γ} {A} {P} {δ} h-idx h-resp h-fam
  module Af = Ap Ft.fold-idx Ft.fold-idx-resp Ft.fold-fam

  record IsFold
      (h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier)
      (h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t'))
      (h-fam : ∀ γ t →
               prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t)) :
      Prop (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    field
      is-idx : ∀ γ x → _≈s_ (A .idx)
               (h-idx γ (Tδ.sup x))
               (alg .idxf .PS._⇒_.func (γ , Ap.apply-shape-idx h-idx h-resp h-fam P γ x))
      is-fam : ∀ γ x →
               h-fam γ (Tδ.sup x)
               ≈ (A .fam .subst (A .idx .isEquivalence .sym (is-idx γ x))
                  ∘ (alg .famf ._⇒f_.transf (γ , Ap.apply-shape-idx h-idx h-resp h-fam P γ x)
                     ∘ pair p₁ (Ap.apply-shape-fam h-idx h-resp h-fam P γ x)))

  -- Index agreement between the fold's recursion and the application at the fold.
  mutual
    agree-shape : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                  _≈s_ (fobj μ-fam Q (extend δ A) .idx) (Ft.fold-shape-idx Q γ x) (Af.apply-shape-idx Q γ x)
    agree-shape (const A')        γ a = A' .idx .isEquivalence .refl
    agree-shape (var Fin.zero)    γ t = A .idx .isEquivalence .refl
    agree-shape (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
    agree-shape (Q₁ + Q₂) γ (inj₁ x) = agree-shape Q₁ γ x
    agree-shape (Q₁ + Q₂) γ (inj₂ y) = agree-shape Q₂ γ y
    agree-shape (Q₁ × Q₂) γ (x , y) = agree-shape Q₁ γ x , agree-shape Q₂ γ y
    agree-shape (μ Q')    γ t = agree-reindex {Q = Q'} γ fbase t

    agree-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d')
                    (t : Tδ.W ∣ Q ∣ ρ) →
                    TA'.W-≈ (Ft.fold-reindex γ fm t) (Af.apply-reindex γ fm t)
    agree-reindex {Q = Q} γ fm (Tδ.sup x) = agree-reindex-shape γ Q (fbind Q fm) x

    agree-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                          (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                          TA'.shape≈ ∣ R ∣ ηB (Ft.fold-reindex-shape γ R fm a) (Af.apply-reindex-shape γ R fm a)
    agree-reindex-shape γ (const A') fm a = A' .idx .isEquivalence .refl
    agree-reindex-shape γ (var v)    fm a = agree-apply γ fm v a
    agree-reindex-shape γ (P' + Q') fm (inj₁ a) = agree-reindex-shape γ P' fm a
    agree-reindex-shape γ (P' + Q') fm (inj₂ b) = agree-reindex-shape γ Q' fm b
    agree-reindex-shape γ (P' × Q') fm (a , b) = agree-reindex-shape γ P' fm a , agree-reindex-shape γ Q' fm b
    agree-reindex-shape γ (μ Q'')   fm t = agree-reindex {Q = Q''} γ fm t

    agree-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                  (a : Tδ.El (ρ v)) →
                  TA'.elEq (ρ' v) (Ft.fold-apply γ fm v a) (Af.apply-apply γ fm v a)
    agree-apply γ fbase        Fin.zero    t = A .idx .isEquivalence .refl
    agree-apply γ fbase        (Fin.suc i) a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
    agree-apply γ (fbind Q fm) Fin.zero    a = agree-reindex {Q = Q} γ fm a
    agree-apply γ (fbind Q fm) (Fin.suc v) a = agree-apply γ fm v a

  -- Fibre agreement: the fold's fibre transported along the index agreement is the application's
  -- fibre. At the value formers the transport passes across the lifting and the congruence closes
  -- on the branch, exactly as in the fold's naturality.
  mutual
    agree-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                      (fobj μ-fam Q (extend δ A) .fam .subst (agree-shape Q γ x) ∘ Ft.fold-shape-fam Q γ x)
                        ≈ Af.apply-shape-fam Q γ x
    agree-shape-fam (const A')        γ a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
    agree-shape-fam (var Fin.zero)    γ t = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    agree-shape-fam (var (Fin.suc i)) γ a = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) id-left
    agree-shape-fam (Q₁ + Q₂) γ (inj₁ x) =
      ≈-trans (under-root-post _
                (Ft.fold-shape-fam Q₁ γ x))
              (under-root-cong (agree-shape-fam Q₁ γ x))
    agree-shape-fam (Q₁ + Q₂) γ (inj₂ y) =
      ≈-trans (under-root-post _
                (Ft.fold-shape-fam Q₂ γ y))
              (under-root-cong (agree-shape-fam Q₂ γ y))
    agree-shape-fam (Q₁ × Q₂) γ (x , y) =
      ≈-trans (under-root-post _
                (strong-prod-m (Ft.fold-shape-fam Q₁ γ x) (Ft.fold-shape-fam Q₂ γ y)))
              (under-root-cong
                (≈-trans (strong-prod-m-post _ _ _ _)
                         (strong-prod-m-cong (agree-shape-fam Q₁ γ x) (agree-shape-fam Q₂ γ y))))
    agree-shape-fam (μ Q') γ t = agree-reindex-fam {Q = Q'} γ fbase t

    agree-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier)
                        (fm : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                        (TA'.fib-subst Q d' {x = Ft.fold-reindex γ fm t} {y = Af.apply-reindex γ fm t}
                           (agree-reindex {Q = Q} γ fm t)
                         ∘ Ft.fold-reindex-fam γ fm t)
                          ≈ Af.apply-reindex-fam γ fm t
    agree-reindex-fam {Q = Q} γ fm (Tδ.sup x) = agree-reindex-shape-fam γ Q (fbind Q fm) x

    agree-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB}
                              (fm : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                              (TA'.fib-shape-subst R dB (agree-reindex-shape γ R fm a)
                               ∘ Ft.fold-reindex-shape-fam γ R fm a)
                                ≈ Af.apply-reindex-shape-fam γ R fm a
    agree-reindex-shape-fam γ (const A') fm a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
    agree-reindex-shape-fam γ (var v)    fm a = agree-apply-fam γ fm v a
    agree-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₁ a) =
      ≈-trans (under-root-post _
                (Ft.fold-reindex-shape-fam γ P' fm a))
              (under-root-cong (agree-reindex-shape-fam γ P' fm a))
    agree-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₂ b) =
      ≈-trans (under-root-post _
                (Ft.fold-reindex-shape-fam γ Q' fm b))
              (under-root-cong (agree-reindex-shape-fam γ Q' fm b))
    agree-reindex-shape-fam γ (P' × Q') {dA = dA} {dB} fm (a , b) =
      ≈-trans (under-root-post _
                (strong-prod-m (Ft.fold-reindex-shape-fam γ P' fm a) (Ft.fold-reindex-shape-fam γ Q' fm b)))
              (under-root-cong
                (≈-trans (strong-prod-m-post _ _ _ _)
                         (strong-prod-m-cong (agree-reindex-shape-fam γ P' fm a)
                                             (agree-reindex-shape-fam γ Q' fm b))))
    agree-reindex-shape-fam γ (μ Q'')   fm t = agree-reindex-fam {Q = Q''} γ fm t

    agree-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                      (a : Tδ.El (ρ v)) →
                      (TA'.fib-el-subst (ρ' v) (d' v) (agree-apply γ fm v a)
                       ∘ Ft.fold-apply-fam γ fm v a)
                        ≈ Af.apply-apply-fam γ fm v a
    agree-apply-fam γ fbase        Fin.zero    t = ≈-trans (∘-cong (A .fam .refl*) ≈-refl) id-left
    agree-apply-fam γ fbase        (Fin.suc i) a =
      ≈-trans (∘-cong (TA'.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) id-left
    agree-apply-fam γ (fbind Q fm) Fin.zero    a = agree-reindex-fam {Q = Q} γ fm a
    agree-apply-fam γ (fbind Q fm) (Fin.suc v) a = agree-apply-fam γ fm v a

  -- The fold satisfies the fused law.
  fold-is-fold : IsFold Ft.fold-idx Ft.fold-idx-resp Ft.fold-fam
  fold-is-fold .IsFold.is-idx γ x =
    alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl , agree-shape P γ x)
  fold-is-fold .IsFold.is-fam γ x =
    ≈-trans (≈-sym id-left)
    (≈-trans (∘-cong (≈-sym (fam-subst-iso₂ (A .fam)
                              (alg .idxf .PS._⇒_.func-resp-≈
                                (Γ .idx .isEquivalence .refl , agree-shape P γ x)))) ≈-refl)
    (≈-trans (assoc _ _ _)
    (∘-cong ≈-refl
      (≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong (≈-sym (alg .famf ._⇒f_.natural
                         (Γ .idx .isEquivalence .refl , agree-shape P γ x))) ≈-refl)
      (≈-trans (assoc _ _ _)
      (∘-cong ≈-refl
        (≈-trans (pair-compose _ _ _ _)
                 (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                            (agree-shape-fam P γ x))))))))))


  -- η: the fused law determines the fold. The comparison of the application at the candidate with
  -- the fold's recursion carries the tree induction at the recursive slots.
  module Eta (h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier)
             (h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                       _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t'))
             (h-fam : ∀ γ t →
                      prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t))
             (H : IsFold h-idx h-resp h-fam) where
    module Ah = Ap h-idx h-resp h-fam

    mutual
      uniq-idx : ∀ γ t → _≈s_ (A .idx) (h-idx γ t) (Ft.fold-idx γ t)
      uniq-idx γ (Tδ.sup x) =
        A .idx .isEquivalence .trans (H .IsFold.is-idx γ x)
          (alg .idxf .PS._⇒_.func-resp-≈ (Γ .idx .isEquivalence .refl , compare-shape P γ x))

      compare-shape : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                    _≈s_ (fobj μ-fam Q (extend δ A) .idx) (Ah.apply-shape-idx Q γ x) (Ft.fold-shape-idx Q γ x)
      compare-shape (const A')        γ a = A' .idx .isEquivalence .refl
      compare-shape (var Fin.zero)    γ t = uniq-idx γ t
      compare-shape (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
      compare-shape (Q₁ + Q₂) γ (inj₁ x) = compare-shape Q₁ γ x
      compare-shape (Q₁ + Q₂) γ (inj₂ y) = compare-shape Q₂ γ y
      compare-shape (Q₁ × Q₂) γ (x , y) = compare-shape Q₁ γ x , compare-shape Q₂ γ y
      compare-shape (μ Q')    γ t = compare-reindex {Q = Q'} γ fbase t

      compare-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d')
                      (t : Tδ.W ∣ Q ∣ ρ) →
                      TA'.W-≈ (Ah.apply-reindex γ fm t) (Ft.fold-reindex γ fm t)
      compare-reindex {Q = Q} γ fm (Tδ.sup x) = compare-reindex-shape γ Q (fbind Q fm) x

      compare-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                            (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                            TA'.shape≈ ∣ R ∣ ηB (Ah.apply-reindex-shape γ R fm a) (Ft.fold-reindex-shape γ R fm a)
      compare-reindex-shape γ (const A') fm a = A' .idx .isEquivalence .refl
      compare-reindex-shape γ (var v)    fm a = compare-apply γ fm v a
      compare-reindex-shape γ (P' + Q') fm (inj₁ a) = compare-reindex-shape γ P' fm a
      compare-reindex-shape γ (P' + Q') fm (inj₂ b) = compare-reindex-shape γ Q' fm b
      compare-reindex-shape γ (P' × Q') fm (a , b) = compare-reindex-shape γ P' fm a , compare-reindex-shape γ Q' fm b
      compare-reindex-shape γ (μ Q'')   fm t = compare-reindex {Q = Q''} γ fm t

      compare-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                    (a : Tδ.El (ρ v)) →
                    TA'.elEq (ρ' v) (Ah.apply-apply γ fm v a) (Ft.fold-apply γ fm v a)
      compare-apply γ fbase        Fin.zero    t = uniq-idx γ t
      compare-apply γ fbase        (Fin.suc i) a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
      compare-apply γ (fbind Q fm) Fin.zero    a = compare-reindex {Q = Q} γ fm a
      compare-apply γ (fbind Q fm) (Fin.suc v) a = compare-apply γ fm v a

    mutual
      uniq-fam : ∀ γ t → (A .fam .subst (uniq-idx γ t) ∘ h-fam γ t) ≈ Ft.fold-fam γ t
      uniq-fam γ (Tδ.sup x) =
        ≈-trans (∘-cong ≈-refl (H .IsFold.is-fam γ x))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (≈-sym (A .fam .trans*
                   (uniq-idx γ (Tδ.sup x))
                   (A .idx .isEquivalence .sym (H .IsFold.is-idx γ x)))) ≈-refl)
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (≈-sym (alg .famf ._⇒f_.natural
                   (Γ .idx .isEquivalence .refl , compare-shape P γ x))) ≈-refl)
        (≈-trans (assoc _ _ _)
        (∘-cong ≈-refl
          (≈-trans (pair-compose _ _ _ _)
                   (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                              (compare-shape-fam P γ x)))))))))

      compare-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                        (fobj μ-fam Q (extend δ A) .fam .subst (compare-shape Q γ x) ∘ Ah.apply-shape-fam Q γ x)
                          ≈ Ft.fold-shape-fam Q γ x
      compare-shape-fam (const A')        γ a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
      compare-shape-fam (var Fin.zero)    γ t = uniq-fam γ t
      compare-shape-fam (var (Fin.suc i)) γ a = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) id-left
      compare-shape-fam (Q₁ + Q₂) γ (inj₁ x) =
        ≈-trans (under-root-post _
                  (Ah.apply-shape-fam Q₁ γ x))
                (under-root-cong (compare-shape-fam Q₁ γ x))
      compare-shape-fam (Q₁ + Q₂) γ (inj₂ y) =
        ≈-trans (under-root-post _
                  (Ah.apply-shape-fam Q₂ γ y))
                (under-root-cong (compare-shape-fam Q₂ γ y))
      compare-shape-fam (Q₁ × Q₂) γ (x , y) =
        ≈-trans (under-root-post _
                  (strong-prod-m (Ah.apply-shape-fam Q₁ γ x) (Ah.apply-shape-fam Q₂ γ y)))
                (under-root-cong
                  (≈-trans (strong-prod-m-post _ _ _ _)
                           (strong-prod-m-cong (compare-shape-fam Q₁ γ x) (compare-shape-fam Q₂ γ y))))
      compare-shape-fam (μ Q') γ t = compare-reindex-fam {Q = Q'} γ fbase t

      compare-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier)
                          (fm : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                          (TA'.fib-subst Q d' {x = Ah.apply-reindex γ fm t} {y = Ft.fold-reindex γ fm t}
                             (compare-reindex {Q = Q} γ fm t)
                           ∘ Ah.apply-reindex-fam γ fm t)
                            ≈ Ft.fold-reindex-fam γ fm t
      compare-reindex-fam {Q = Q} γ fm (Tδ.sup x) = compare-reindex-shape-fam γ Q (fbind Q fm) x

      compare-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB}
                                (fm : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                                (TA'.fib-shape-subst R dB (compare-reindex-shape γ R fm a)
                                 ∘ Ah.apply-reindex-shape-fam γ R fm a)
                                  ≈ Ft.fold-reindex-shape-fam γ R fm a
      compare-reindex-shape-fam γ (const A') fm a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
      compare-reindex-shape-fam γ (var v)    fm a = compare-apply-fam γ fm v a
      compare-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₁ a) =
        ≈-trans (under-root-post _
                  (Ah.apply-reindex-shape-fam γ P' fm a))
                (under-root-cong (compare-reindex-shape-fam γ P' fm a))
      compare-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₂ b) =
        ≈-trans (under-root-post _
                  (Ah.apply-reindex-shape-fam γ Q' fm b))
                (under-root-cong (compare-reindex-shape-fam γ Q' fm b))
      compare-reindex-shape-fam γ (P' × Q') {dA = dA} {dB} fm (a , b) =
        ≈-trans (under-root-post _
                  (strong-prod-m (Ah.apply-reindex-shape-fam γ P' fm a) (Ah.apply-reindex-shape-fam γ Q' fm b)))
                (under-root-cong
                  (≈-trans (strong-prod-m-post _ _ _ _)
                           (strong-prod-m-cong (compare-reindex-shape-fam γ P' fm a)
                                               (compare-reindex-shape-fam γ Q' fm b))))
      compare-reindex-shape-fam γ (μ Q'')   fm t = compare-reindex-fam {Q = Q''} γ fm t

      compare-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                        (a : Tδ.El (ρ v)) →
                        (TA'.fib-el-subst (ρ' v) (d' v) (compare-apply γ fm v a)
                         ∘ Ah.apply-apply-fam γ fm v a)
                          ≈ Ft.fold-apply-fam γ fm v a
      compare-apply-fam γ fbase        Fin.zero    t = uniq-fam γ t
      compare-apply-fam γ fbase        (Fin.suc i) a =
        ≈-trans (∘-cong (TA'.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) id-left
      compare-apply-fam γ (fbind Q fm) Fin.zero    a = compare-reindex-fam {Q = Q} γ fm a
      compare-apply-fam γ (fbind Q fm) (Fin.suc v) a = compare-apply-fam γ fm v a


  -- Morphism-level packaging: the fused law for a candidate given as a family morphism, the fold
  -- satisfying it and being the only solution. The transports in the morphism equality carry
  -- proposition-valued proofs, so the pointwise statements apply directly.
  IsFoldMor : (h : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A) → Prop (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es)
  IsFoldMor h =
    IsFold (λ γ t → h .idxf .PS._⇒_.func (γ , t))
           (λ γ≈ p → h .idxf .PS._⇒_.func-resp-≈ (γ≈ , p))
           (λ γ t → h .famf ._⇒f_.transf (γ , t))

  ⦅⦆-β : IsFoldMor (FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg)
  ⦅⦆-β .IsFold.is-idx = fold-is-fold .IsFold.is-idx
  ⦅⦆-β .IsFold.is-fam = fold-is-fold .IsFold.is-fam

  ⦅⦆-η : (h : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A) → IsFoldMor h →
         h ≃ FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg
  ⦅⦆-η h H = go
    where
    module E = Eta (λ γ t → h .idxf .PS._⇒_.func (γ , t))
                   (λ γ≈ p → h .idxf .PS._⇒_.func-resp-≈ (γ≈ , p))
                   (λ γ t → h .famf ._⇒f_.transf (γ , t)) H

    go : h ≃ FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg
    go ._≃_.idxf-eq .PS._≃m_.func-eq {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) =
      A .idx .isEquivalence .trans (E.uniq-idx γ₁ t₁) (Ft.fold-idx-resp γ≈ {t₁} {t₂} t≈)
    go ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , t} = E.uniq-fam γ t

  -- The fold is congruent in its algebra, the congruence entering at the top of every node.
  module FoldCong (alg' : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A) (E : alg ≃ alg') where
    module Ft' = FoldDef {n} {Γ} {A} {P} {δ} alg'

    mutual
      fc-idx : ∀ γ t → _≈s_ (A .idx) (Ft.fold-idx γ t) (Ft'.fold-idx γ t)
      fc-idx γ (Tδ.sup x) =
        E ._≃_.idxf-eq .PS._≃m_.func-eq (Γ .idx .isEquivalence .refl , fc-shape P γ x)

      fc-shape : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                    _≈s_ (fobj μ-fam Q (extend δ A) .idx) (Ft.fold-shape-idx Q γ x) (Ft'.fold-shape-idx Q γ x)
      fc-shape (const A')        γ a = A' .idx .isEquivalence .refl
      fc-shape (var Fin.zero)    γ t = fc-idx γ t
      fc-shape (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
      fc-shape (Q₁ + Q₂) γ (inj₁ x) = fc-shape Q₁ γ x
      fc-shape (Q₁ + Q₂) γ (inj₂ y) = fc-shape Q₂ γ y
      fc-shape (Q₁ × Q₂) γ (x , y) = fc-shape Q₁ γ x , fc-shape Q₂ γ y
      fc-shape (μ Q')    γ t = fc-reindex {Q = Q'} γ fbase t

      fc-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d')
                      (t : Tδ.W ∣ Q ∣ ρ) →
                      TA'.W-≈ (Ft.fold-reindex γ fm t) (Ft'.fold-reindex γ fm t)
      fc-reindex {Q = Q} γ fm (Tδ.sup x) = fc-reindex-shape γ Q (fbind Q fm) x

      fc-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                            (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                            TA'.shape≈ ∣ R ∣ ηB (Ft.fold-reindex-shape γ R fm a) (Ft'.fold-reindex-shape γ R fm a)
      fc-reindex-shape γ (const A') fm a = A' .idx .isEquivalence .refl
      fc-reindex-shape γ (var v)    fm a = fc-apply γ fm v a
      fc-reindex-shape γ (P' + Q') fm (inj₁ a) = fc-reindex-shape γ P' fm a
      fc-reindex-shape γ (P' + Q') fm (inj₂ b) = fc-reindex-shape γ Q' fm b
      fc-reindex-shape γ (P' × Q') fm (a , b) = fc-reindex-shape γ P' fm a , fc-reindex-shape γ Q' fm b
      fc-reindex-shape γ (μ Q'')   fm t = fc-reindex {Q = Q''} γ fm t

      fc-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                    (a : Tδ.El (ρ v)) →
                    TA'.elEq (ρ' v) (Ft.fold-apply γ fm v a) (Ft'.fold-apply γ fm v a)
      fc-apply γ fbase        Fin.zero    t = fc-idx γ t
      fc-apply γ fbase        (Fin.suc i) a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
      fc-apply γ (fbind Q fm) Fin.zero    a = fc-reindex {Q = Q} γ fm a
      fc-apply γ (fbind Q fm) (Fin.suc v) a = fc-apply γ fm v a

    mutual
      fc-fam : ∀ γ t → (A .fam .subst (fc-idx γ t) ∘ Ft.fold-fam γ t) ≈ Ft'.fold-fam γ t
      fc-fam γ (Tδ.sup x) =
        ≈-trans (∘-cong (A .fam .trans*
                  (alg' .idxf .PS._⇒_.func-resp-≈
                    (Γ .idx .isEquivalence .refl , fc-shape P γ x))
                  (E ._≃_.idxf-eq .PS._≃m_.func-eq
                    (Γ .idx .isEquivalence .refl ,
                     fobj μ-fam P (extend δ A) .idx .isEquivalence .refl))) ≈-refl)
        (≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl
                   (≈-trans (≈-sym (assoc _ _ _))
                    (∘-cong (E ._≃_.famf-eq .indexed-family._≃f_.transf-eq) ≈-refl)))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (≈-sym (alg' .famf ._⇒f_.natural
                   (Γ .idx .isEquivalence .refl , fc-shape P γ x))) ≈-refl)
        (≈-trans (assoc _ _ _)
        (∘-cong ≈-refl
          (≈-trans (pair-compose _ _ _ _)
                   (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left)
                              (fc-shape-fam P γ x)))))))))

      fc-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                        (fobj μ-fam Q (extend δ A) .fam .subst (fc-shape Q γ x) ∘ Ft.fold-shape-fam Q γ x)
                          ≈ Ft'.fold-shape-fam Q γ x
      fc-shape-fam (const A')        γ a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
      fc-shape-fam (var Fin.zero)    γ t = fc-fam γ t
      fc-shape-fam (var (Fin.suc i)) γ a = ≈-trans (∘-cong (δ i .fam .refl*) ≈-refl) id-left
      fc-shape-fam (Q₁ + Q₂) γ (inj₁ x) =
        ≈-trans (under-root-post _
                  (Ft.fold-shape-fam Q₁ γ x))
                (under-root-cong (fc-shape-fam Q₁ γ x))
      fc-shape-fam (Q₁ + Q₂) γ (inj₂ y) =
        ≈-trans (under-root-post _
                  (Ft.fold-shape-fam Q₂ γ y))
                (under-root-cong (fc-shape-fam Q₂ γ y))
      fc-shape-fam (Q₁ × Q₂) γ (x , y) =
        ≈-trans (under-root-post _
                  (strong-prod-m (Ft.fold-shape-fam Q₁ γ x) (Ft.fold-shape-fam Q₂ γ y)))
                (under-root-cong
                  (≈-trans (strong-prod-m-post _ _ _ _)
                           (strong-prod-m-cong (fc-shape-fam Q₁ γ x) (fc-shape-fam Q₂ γ y))))
      fc-shape-fam (μ Q') γ t = fc-reindex-fam {Q = Q'} γ fbase t

      fc-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier)
                          (fm : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                          (TA'.fib-subst Q d' {x = Ft.fold-reindex γ fm t} {y = Ft'.fold-reindex γ fm t}
                             (fc-reindex {Q = Q} γ fm t)
                           ∘ Ft.fold-reindex-fam γ fm t)
                            ≈ Ft'.fold-reindex-fam γ fm t
      fc-reindex-fam {Q = Q} γ fm (Tδ.sup x) = fc-reindex-shape-fam γ Q (fbind Q fm) x

      fc-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB}
                                (fm : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                                (TA'.fib-shape-subst R dB (fc-reindex-shape γ R fm a)
                                 ∘ Ft.fold-reindex-shape-fam γ R fm a)
                                  ≈ Ft'.fold-reindex-shape-fam γ R fm a
      fc-reindex-shape-fam γ (const A') fm a = ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) id-left
      fc-reindex-shape-fam γ (var v)    fm a = fc-apply-fam γ fm v a
      fc-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₁ a) =
        ≈-trans (under-root-post _
                  (Ft.fold-reindex-shape-fam γ P' fm a))
                (under-root-cong (fc-reindex-shape-fam γ P' fm a))
      fc-reindex-shape-fam γ (P' + Q') {dA = dA} {dB} fm (inj₂ b) =
        ≈-trans (under-root-post _
                  (Ft.fold-reindex-shape-fam γ Q' fm b))
                (under-root-cong (fc-reindex-shape-fam γ Q' fm b))
      fc-reindex-shape-fam γ (P' × Q') {dA = dA} {dB} fm (a , b) =
        ≈-trans (under-root-post _
                  (strong-prod-m (Ft.fold-reindex-shape-fam γ P' fm a) (Ft.fold-reindex-shape-fam γ Q' fm b)))
                (under-root-cong
                  (≈-trans (strong-prod-m-post _ _ _ _)
                           (strong-prod-m-cong (fc-reindex-shape-fam γ P' fm a)
                                               (fc-reindex-shape-fam γ Q' fm b))))
      fc-reindex-shape-fam γ (μ Q'')   fm t = fc-reindex-fam {Q = Q''} γ fm t

      fc-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k)
                        (a : Tδ.El (ρ v)) →
                        (TA'.fib-el-subst (ρ' v) (d' v) (fc-apply γ fm v a)
                         ∘ Ft.fold-apply-fam γ fm v a)
                          ≈ Ft'.fold-apply-fam γ fm v a
      fc-apply-fam γ fbase        Fin.zero    t = fc-fam γ t
      fc-apply-fam γ fbase        (Fin.suc i) a =
        ≈-trans (∘-cong (TA'.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) id-left
      fc-apply-fam γ (fbind Q fm) Fin.zero    a = fc-reindex-fam {Q = Q} γ fm a
      fc-apply-fam γ (fbind Q fm) (Fin.suc v) a = fc-apply-fam γ fm v a


    ⦅⦆-cong : FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg ≃ FoldDef.foldMor {n} {Γ} {A} {P} {δ} alg'
    ⦅⦆-cong ._≃_.idxf-eq .PS._≃m_.func-eq {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) =
      A .idx .isEquivalence .trans (fc-idx γ₁ t₁) (Ft'.fold-idx-resp γ≈ {t₁} {t₂} t≈)
    ⦅⦆-cong ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , t} = fc-fam γ t

-- The strong actions are congruent in the environment maps, the μ-case through the fold's
-- congruence in its algebra.
private module FMuC = HasMu hasMu

mutual
  strong-fmor-cong : ∀ {k} {Γ : Obj} (P : Poly k) {δ δ' : Fin k → Obj}
                     {fs gs : ∀ i → Mor (Fam𝒞-P.prod Γ (δ i)) (δ' i)} →
                     (∀ i → fs i ≃ gs i) →
                     FMuC.strong-fmor P fs ≃ FMuC.strong-fmor P gs
  strong-fmor-cong (const A) es = Fam𝒞.≈-refl
  strong-fmor-cong (var i)   es = es i
  strong-fmor-cong (P' + Q') es =
    HasStrongCoproducts.copair-cong strongCoproducts
      (Fam𝒞.∘-cong Fam𝒞.≈-refl (under-rootF-cong (strong-fmor-cong P' es)))
      (Fam𝒞.∘-cong Fam𝒞.≈-refl (under-rootF-cong (strong-fmor-cong Q' es)))
  strong-fmor-cong (P' × Q') es =
    under-rootF-cong (Fam𝒞-P.strong-prod-m-cong (strong-fmor-cong P' es) (strong-fmor-cong Q' es))
  strong-fmor-cong (μ P')    es = strong-μ-fmor-cong P' es

  strong-μ-fmor-cong : ∀ {k} {Γ : Obj} (P : Poly (suc k)) {δ δ' : Fin k → Obj}
                       {fs gs : ∀ i → Mor (Fam𝒞-P.prod Γ (δ i)) (δ' i)} →
                       (∀ i → fs i ≃ gs i) →
                       FMuC.strong-μ-fmor P fs ≃ FMuC.strong-μ-fmor P gs
  strong-μ-fmor-cong {k} {Γ} P {δ} {δ'} {fs} {gs} es =
    Laws.FoldCong.⦅⦆-cong {k} {Γ} {FMuC.μ-obj P δ'} {P} {δ}
      (Fam𝒞._∘_ (FMuC.inMap P δ') (FMuC.strong-fmor P (FMuC.strong-extend-mor fs Fam𝒞-P.p₂)))
      (Fam𝒞._∘_ (FMuC.inMap P δ') (FMuC.strong-fmor P (FMuC.strong-extend-mor gs Fam𝒞-P.p₂)))
      (Fam𝒞.∘-cong Fam𝒞.≈-refl
        (strong-fmor-cong P (λ { Fin.zero → Fam𝒞.≈-refl ; (Fin.suc i) → es i })))

-- Reflection, index half: applying the intro algebra's data at the projection candidate and
-- carrying the result back through the bridges is the identity on trees. The relation pairs each
-- fold-reindex morphism with the bridge reindex that undoes it.
module Reflection {n} {Γ : Obj} {P : Poly (suc n)} {δ : Fin n → Obj} where
  private module At = InMapDef P δ
  open FoldBase {n} {Γ} {μ-fam P δ} {P} {δ}

  algR : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ (μ-fam P δ)))) (μ-fam P δ)
  algR = Fam𝒞._∘_ At.inMor (Fam𝒞-P.p₂ {Γ} {fobj μ-fam P (extend δ (μ-fam P δ))})

  module L' = Laws {n} {Γ} {μ-fam P δ} {P} {δ} algR
  module Ah = L'.Ap (λ γ t → t) (λ γ≈ p → p)
                (λ γ t → Fam𝒞-P.p₂ {Γ} {μ-fam P δ} .famf ._⇒f_.transf (γ , t))

  data RRel : ∀ {j} {ρ : Fin j → Fin n ⊎ Sort n} {ρ' : Fin j → Fin (suc n) ⊎ Sort (suc n)}
              {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → TA'.DecoAssign (ρ' v)} →
              FMor ρ ρ' d d' → At.R.MorD ρ' ρ d' d →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    rbase : RRel fbase At.mor₀
    rbind : ∀ {j} {ρ ρ' d d'} {fm : FMor {j} ρ ρ' d d'} {md} (Q' : Poly (suc j)) →
            RRel fm md → RRel (fbind Q' fm) (At.R.bind Q' md)

  mutual
    ra-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {fm : FMor ρ ρ' d d'} {md} → RRel fm md →
           (γ : Γ .idx .Carrier) (t : Tδ.W ∣ Q̂ ∣ ρ) →
           Tδ.W-≈ (At.R.reindex md (Ah.apply-reindex γ fm t)) t
    ra-W {Q̂ = Q̂} rel γ (Tδ.sup x) = ra-shape Q̂ (rbind Q̂ rel) γ x

    ra-shape : ∀ {j} (R : Poly j) {ρ : Fin j → Fin n ⊎ Sort n} {ρ'} {d d'}
               {fm : FMor ρ ρ' d d'} {md : At.R.MorD ρ' ρ d' d} → RRel fm md →
               (γ : Γ .idx .Carrier) (a : Tδ.⟦ ∣ R ∣ ⟧shape ρ) →
               Tδ.shape≈ ∣ R ∣ ρ (At.R.reindex-shape ∣ R ∣ md (Ah.apply-reindex-shape γ R fm a)) a
    ra-shape (const A') rel γ a = A' .idx .isEquivalence .refl
    ra-shape (var v)    rel γ a = ra-el rel γ v a
    ra-shape (P' + Q') rel γ (inj₁ a) = ra-shape P' rel γ a
    ra-shape (P' + Q') rel γ (inj₂ b) = ra-shape Q' rel γ b
    ra-shape (P' × Q') rel γ (a , b) = ra-shape P' rel γ a , ra-shape Q' rel γ b
    ra-shape (μ Q'')   rel γ t = ra-W {Q̂ = Q''} rel γ t

    ra-el : ∀ {j} {ρ ρ' d d'} {fm : FMor {j} ρ ρ' d d'} {md} → RRel fm md →
            (γ : Γ .idx .Carrier) (v : Fin j) (a : Tδ.El (ρ v)) →
            Tδ.elEq (ρ v) (At.R.apply md v (Ah.apply-apply γ fm v a)) a
    ra-el rbase          γ Fin.zero    t = Tδ.elEq-refl (Srt.η₀ ∣ P ∣ Fin.zero) t
    ra-el rbase          γ (Fin.suc i) a = Tδ.elEq-refl (Srt.η₀ ∣ P ∣ (Fin.suc i)) a
    ra-el (rbind Q' rel) γ Fin.zero    a = ra-W {Q̂ = Q'} rel γ a
    ra-el (rbind Q' rel) γ (Fin.suc v) a = ra-el rel γ v a

  -- The top-level round trip through the embed bridge.
  ra-top : ∀ (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
           Tδ.shape≈ ∣ Q ∣ (Srt.η₀ ∣ P ∣)
             (At.R.reindex-shape ∣ Q ∣ At.mor₀ (At.embed-idx Q (Ah.apply-shape-idx Q γ x))) x
  ra-top (const A')        γ a = A' .idx .isEquivalence .refl
  ra-top (var Fin.zero)    γ t = Tδ.elEq-refl (Srt.η₀ ∣ P ∣ Fin.zero) t
  ra-top (var (Fin.suc i)) γ a = Tδ.elEq-refl (Srt.η₀ ∣ P ∣ (Fin.suc i)) a
  ra-top (Q₁ + Q₂) γ (inj₁ x) = ra-top Q₁ γ x
  ra-top (Q₁ + Q₂) γ (inj₂ y) = ra-top Q₂ γ y
  ra-top (Q₁ × Q₂) γ (x , y) = ra-top Q₁ γ x , ra-top Q₂ γ y
  ra-top (μ Q')    γ t = ra-W {Q̂ = Q'} rbase γ t

  -- The projection's index component satisfies the fused law's index half at the intro algebra.
  reflection-idx : ∀ (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ P ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                   _≈s_ (μ-fam P δ .idx) (Tδ.sup x)
                        (algR .idxf .PS._⇒_.func (γ , Ah.apply-shape-idx P γ x))
  reflection-idx γ x = Tδ.shape≈-sym ∣ P ∣ (Srt.η₀ ∣ P ∣) (ra-top P γ x)

module Bridge {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (h : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A) where
  open FoldBase {n} {Γ} {A} {P} {δ}
  private
    module At = InMapDef P δ
    module TX = Tree At.δ'
    module RX = Reindex At.δ' (extend δ A)

  h-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier
  h-idx γ t = h .idxf .PS._⇒_.func (γ , t)

  h-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') → _≈s_ (A .idx) (h-idx γ t) (h-idx γ' t')
  h-resp γ≈ p = h .idxf .PS._⇒_.func-resp-≈ (γ≈ , p)

  h-fam : ∀ γ t → prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (h-idx γ t)
  h-fam γ t = h .famf ._⇒f_.transf (γ , t)

  open ApplyDef {n} {Γ} {A} {P} {δ} h-idx h-resp h-fam public

  fs : ∀ i → Mor (Fam𝒞-P.prod Γ (At.δ' i)) (extend δ A i)
  fs = FMuC.strong-extend-mor (λ i → Fam𝒞-P.p₂) h

  -- Reindexing along the candidate at the recursion slot and the identity at the parameters.
  cmb : Γ .idx .Carrier → RX.IMorD (λ v → inj₁ v) (λ v → inj₁ v)
  cmb γ = RX.ibase (λ { Fin.zero t → h-idx γ t ; (Fin.suc i) a → a })
                   (λ { Fin.zero p → h-resp (Γ .idx .isEquivalence .refl) p ; (Fin.suc i) p → p })

  -- The application after the bridge reindexing, paired with the one reindexing they compose to.
  data CRel (γ : Γ .idx .Carrier) :
            ∀ {j} {ρX : Fin j → Fin (suc n) ⊎ Sort (suc n)} {ρ : Fin j → Fin n ⊎ Sort n}
            {ρ' : Fin j → Fin (suc n) ⊎ Sort (suc n)}
            {dX : ∀ v → TX.DecoAssign (ρX v)} {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → TA'.DecoAssign (ρ' v)} →
            FMor ρ ρ' d d' → At.R.MorD ρX ρ dX d → RX.IMorD ρX ρ' →
            Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    cbase : CRel γ fbase At.mor₀ (cmb γ)
    cbind : ∀ {j} {ρX ρ ρ' dX d d'} {fm : FMor {j} ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im}
            (Q : Poly (suc j)) → CRel γ fm md im →
            CRel γ (fbind Q fm) (At.R.bind Q md) (RX.ibind ∣ Q ∣ im)

  mutual
    comp-W : ∀ {γ} {j} {Q̂ : Poly (suc j)} {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im} →
             CRel γ fm md im → (t : TX.W ∣ Q̂ ∣ ρX) →
             TA'.W-≈ (apply-reindex {Q = Q̂} γ fm (At.R.reindex md t)) (RX.ireindex im t)
    comp-W {Q̂ = Q̂} rel (TX.sup x) = comp-shape Q̂ (cbind Q̂ rel) x

    comp-shape : ∀ {γ} {j} (S : Poly j) {ρX ρ ρ' dX d d'} {fm : FMor ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im} →
                 CRel γ fm md im → (a : TX.⟦ ∣ S ∣ ⟧shape ρX) →
                 TA'.shape≈ ∣ S ∣ ρ' (apply-reindex-shape γ S fm (At.R.reindex-shape ∣ S ∣ md a)) (RX.ireindex-shape ∣ S ∣ im a)
    comp-shape (const A') rel a = A' .idx .isEquivalence .refl
    comp-shape (var v)    rel a = comp-el rel v a
    comp-shape (P' + Q') rel (inj₁ a) = comp-shape P' rel a
    comp-shape (P' + Q') rel (inj₂ b) = comp-shape Q' rel b
    comp-shape (P' × Q') rel (a , b) = comp-shape P' rel a , comp-shape Q' rel b
    comp-shape (μ Q'')   rel t = comp-W {Q̂ = Q''} rel t

    comp-el : ∀ {γ} {j} {ρX ρ ρ' dX d d'} {fm : FMor {j} ρ ρ' d d'} {md : At.R.MorD ρX ρ dX d} {im} →
              CRel γ fm md im → (v : Fin j) (a : TX.El (ρX v)) →
              TA'.elEq (ρ' v) (apply-apply γ fm v (At.R.apply md v a)) (RX.iapply im v a)
    comp-el cbase          Fin.zero    t = A .idx .isEquivalence .refl
    comp-el cbase          (Fin.suc i) a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
    comp-el (cbind Q rel)  Fin.zero    a = comp-W {Q̂ = Q} rel a
    comp-el (cbind Q rel)  (Fin.suc v) a = comp-el rel v a

  -- The candidate applied at the shape under the algebra map is the strong action, on indices.
  bridge-idx : ∀ (Q : Poly (suc n)) γ (y : fobj μ-fam Q At.δ' .idx .Carrier) →
               _≈s_ (fobj μ-fam Q (extend δ A) .idx)
                 (apply-shape-idx Q γ (At.R.reindex-shape ∣ Q ∣ At.mor₀ (At.embed-idx Q y)))
                 (FMuC.strong-fmor Q fs .idxf .PS._⇒_.func (γ , y))
  bridge-idx (const A')        γ a = A' .idx .isEquivalence .refl
  bridge-idx (var Fin.zero)    γ t = A .idx .isEquivalence .refl
  bridge-idx (var (Fin.suc i)) γ a = δ i .idx .isEquivalence .refl
  bridge-idx (Q₁ + Q₂) γ (inj₁ y) = bridge-idx Q₁ γ y
  bridge-idx (Q₁ + Q₂) γ (inj₂ y) = bridge-idx Q₂ γ y
  bridge-idx (Q₁ × Q₂) γ (y₁ , y₂) = bridge-idx Q₁ γ y₁ , bridge-idx Q₂ γ y₂
  bridge-idx (μ Q') γ t =
    TA'.W-≈-trans {x = apply-reindex {Q = Q'} γ fbase (At.R.reindex At.mor₀ t)} {y = RX.ireindex (cmb γ) t}
      (comp-W cbase t)
      (fuse-idx {Γ = Γ} {sₛ = At.δ'} {sₜ = extend δ A} Q' cmb fs
         (λ { Fin.zero γ≈ {a₁} {a₂} a≈ → h-resp γ≈ {a₁} {a₂} a≈ ; (Fin.suc i) γ≈ a≈ → a≈ })
         (Γ .idx .isEquivalence .refl) {m₁ = t} {m₂ = t} (TX.W-≈-refl t))

-- β on indices: the fold after the algebra map is the algebra after the strong action of the fold.
module BetaIdx {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
    (alg : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
  private
    module At = InMapDef P δ
    module Ft = FoldDef {n} {Γ} {A} {P} {δ} alg
    module L = Laws {n} {Γ} {A} {P} {δ} alg
  open Bridge {n} {Γ} {A} {P} {δ} Ft.foldMor

  β-idx : ∀ γ y → _≈s_ (A .idx)
            (Ft.fold-idx γ (At.inMor .idxf .PS._⇒_.func y))
            (alg .idxf .PS._⇒_.func (γ , FMuC.strong-fmor P fs .idxf .PS._⇒_.func (γ , y)))
  β-idx γ y =
    alg .idxf .PS._⇒_.func-resp-≈
      (Γ .idx .isEquivalence .refl ,
       fobj μ-fam P (extend δ A) .idx .isEquivalence .trans
         (L.agree-shape P γ (At.R.reindex-shape ∣ P ∣ At.mor₀ (At.embed-idx P y)))
         (bridge-idx P γ y))
