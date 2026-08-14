{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The strong catamorphism: folding a μ-carrier in an ambient context Γ, so no
-- exponentials are required. FMor is the fold-specific reindex morphism, again
-- first-order for termination, carrying the decorations of both sides.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import prop-setoid as PS using ()
open import indexed-family using (_⇒f_)
import fam-mu-lifting.reindex

module fam-mu-lifting.fold {o m e} (os es : Level) {𝒞 : Category o m e}
    (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    (𝟙c : Category.obj 𝒞) where

open fam-mu-lifting.reindex os es CM BP 𝟙c public

-- The fold (catamorphism) for the μ-type, lifted to a standalone module so its
-- mutual recursion is termination-checked independently of the `hasMu` copattern.
-- The fold-specific reindex morphism, shared by the fold and by the application of an algebra to a
-- candidate: `fbase` sends the outer recursion slot to the recursive map and parameters to
-- themselves; `fbind` records a binder.
module FoldBase {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj} where
    module Tδ = Tree δ
    module TA' = Tree (extend δ A)
    data FMor : ∀ {k} (ρ : Fin k → Fin n ⊎ Sort n) (ρ' : Fin k → Fin (suc n) ⊎ Sort (suc n)) →
                (∀ v → Tδ.DecoAssign (ρ v)) → (∀ v → TA'.DecoAssign (ρ' v)) →
                Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      fbase : FMor (Srt.η₀ ∣ P ∣) (λ v → inj₁ v)
                   (Tδ.deco-ext P {ρ̄ = λ i → inj₁ i} (λ i → lift tt)) (λ v → lift tt)
      fbind : ∀ {k} {ρ ρ' d d'} (Q : Poly (suc k)) → FMor ρ ρ' d d' →
              FMor (extend ρ (inj₂ (mkSort ∣ Q ∣ ρ))) (extend ρ' (inj₂ (mkSort ∣ Q ∣ ρ')))
                   (Tδ.deco-ext Q d) (TA'.deco-ext Q d')

module FoldDef {n} {Γ A : Obj} {P : Poly (suc n)} {δ : Fin n → Obj}
               (alg : Mor (Fam𝒞-P.prod Γ (fobj μ-fam P (extend δ A))) A) where
    open FoldBase {n} {Γ} {A} {P} {δ} public
    -- Fold the outer μ via `alg`; nested μ are reindexed into the `extend δ A` context,
    -- the recursion slot carrying the fold itself (inlined, so every call is structural).
    mutual
      fold-idx : Γ .idx .Carrier → Tδ.W ∣ P ∣ (λ i → inj₁ i) → A .idx .Carrier
      fold-idx γ (Tδ.sup x) = alg .idxf .PS._⇒_.func (γ , fold-shape-idx P γ x)

      fold-shape-idx : (Q : Poly (suc n)) → Γ .idx .Carrier → Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣) →
                      fobj μ-fam Q (extend δ A) .idx .Carrier
      fold-shape-idx (const A')        γ a = a
      fold-shape-idx (var Fin.zero)    γ t = fold-idx γ t
      fold-shape-idx (var (Fin.suc i)) γ a = a
      fold-shape-idx (Q₁ + Q₂) γ (inj₁ x) = inj₁ (fold-shape-idx Q₁ γ x)
      fold-shape-idx (Q₁ + Q₂) γ (inj₂ y) = inj₂ (fold-shape-idx Q₂ γ y)
      fold-shape-idx (Q₁ × Q₂) γ (x , y) = fold-shape-idx Q₁ γ x , fold-shape-idx Q₂ γ y
      fold-shape-idx (μ Q')    γ t = fold-reindex {Q = Q'} γ fbase t

      fold-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') →
                     Tδ.W ∣ Q ∣ ρ → TA'.W ∣ Q ∣ ρ'
      fold-reindex {Q = Q} γ fm (Tδ.sup x) = TA'.sup (fold-reindex-shape γ Q (fbind Q fm) x)

      fold-reindex-shape : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB) →
                           Tδ.⟦ ∣ R ∣ ⟧shape ηA → TA'.⟦ ∣ R ∣ ⟧shape ηB
      fold-reindex-shape γ (const A') fm a = a
      fold-reindex-shape γ (var v)    fm a = fold-apply γ fm v a
      fold-reindex-shape γ (P' + Q') fm (inj₁ a) = inj₁ (fold-reindex-shape γ P' fm a)
      fold-reindex-shape γ (P' + Q') fm (inj₂ b) = inj₂ (fold-reindex-shape γ Q' fm b)
      fold-reindex-shape γ (P' × Q') fm (a , b) = fold-reindex-shape γ P' fm a , fold-reindex-shape γ Q' fm b
      fold-reindex-shape γ (μ Q'')   fm t = fold-reindex {Q = Q''} γ fm t

      fold-apply : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (fm : FMor ρ ρ' d d') (v : Fin k) →
                   Tδ.El (ρ v) → TA'.El (ρ' v)
      fold-apply γ fbase        Fin.zero    t = fold-idx γ t
      fold-apply γ fbase        (Fin.suc i) a = a
      fold-apply γ (fbind Q fm) Fin.zero    a = fold-reindex {Q = Q} γ fm a
      fold-apply γ (fbind Q fm) (Fin.suc v) a = fold-apply γ fm v a

    -- The index fold respects ≈ (in both Γ and the tree).
    mutual
      fold-idx-resp : ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {t t'} (p : Tδ.W-≈ t t') →
                      _≈s_ (A .idx) (fold-idx γ t) (fold-idx γ' t')
      fold-idx-resp γ≈ {Tδ.sup x} {Tδ.sup y} p = alg .idxf .PS._⇒_.func-resp-≈ (γ≈ , fold-shape-idx-resp P γ≈ p)

      fold-shape-idx-resp : (Q : Poly (suc n)) → ∀ {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') {x x'}
                           (p : Tδ.shape≈ ∣ Q ∣ (Srt.η₀ ∣ P ∣) x x') →
                           _≈s_ (fobj μ-fam Q (extend δ A) .idx) (fold-shape-idx Q γ x) (fold-shape-idx Q γ' x')
      fold-shape-idx-resp (const A')        γ≈ p = p
      fold-shape-idx-resp (var Fin.zero)    γ≈ {x} {x'} p = fold-idx-resp γ≈ {x} {x'} p
      fold-shape-idx-resp (var (Fin.suc i)) γ≈ p = p
      fold-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₁ _} {inj₁ _} p = fold-shape-idx-resp Q₁ γ≈ p
      fold-shape-idx-resp (Q₁ + Q₂) γ≈ {inj₂ _} {inj₂ _} p = fold-shape-idx-resp Q₂ γ≈ p
      fold-shape-idx-resp (Q₁ × Q₂) γ≈ {_ , _} {_ , _} (p₁ , p₂) =
        fold-shape-idx-resp Q₁ γ≈ p₁ , fold-shape-idx-resp Q₂ γ≈ p₂
      fold-shape-idx-resp (μ Q')    γ≈ {x} {x'} p = fold-reindex-resp {Q = Q'} γ≈ fbase {x} {x'} p

      fold-reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d')
                          {t t' : Tδ.W ∣ Q ∣ ρ} (p : Tδ.W-≈ t t') →
                          TA'.W-≈ (fold-reindex γ fm t) (fold-reindex γ' fm t')
      fold-reindex-resp {Q = Q} γ≈ fm {Tδ.sup x} {Tδ.sup y} p = fold-reindex-shape-resp γ≈ Q (fbind Q fm) {x} {y} p

      fold-reindex-shape-resp : ∀ {j} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (R : Poly j) {ηA ηB dA dB} (fm : FMor ηA ηB dA dB)
                                {a a' : Tδ.⟦ ∣ R ∣ ⟧shape ηA} (p : Tδ.shape≈ ∣ R ∣ ηA a a') →
                                TA'.shape≈ ∣ R ∣ ηB (fold-reindex-shape γ R fm a) (fold-reindex-shape γ' R fm a')
      fold-reindex-shape-resp γ≈ (const A') fm p = p
      fold-reindex-shape-resp γ≈ (var v)    fm p = fold-apply-resp γ≈ fm v p
      fold-reindex-shape-resp γ≈ (P' + Q') fm {inj₁ _} {inj₁ _} p = fold-reindex-shape-resp γ≈ P' fm p
      fold-reindex-shape-resp γ≈ (P' + Q') fm {inj₂ _} {inj₂ _} p = fold-reindex-shape-resp γ≈ Q' fm p
      fold-reindex-shape-resp γ≈ (P' × Q') fm {_ , _} {_ , _} (p₁ , p₂) =
        fold-reindex-shape-resp γ≈ P' fm p₁ , fold-reindex-shape-resp γ≈ Q' fm p₂
      fold-reindex-shape-resp γ≈ (μ Q'')   fm {a} {a'} p = fold-reindex-resp {Q = Q''} γ≈ fm {a} {a'} p

      fold-apply-resp : ∀ {k} {ρ ρ' d d'} {γ γ'} (γ≈ : _≈s_ (Γ .idx) γ γ') (fm : FMor ρ ρ' d d') (v : Fin k)
                        {a a'} (p : Tδ.elEq (ρ v) a a') →
                        TA'.elEq (ρ' v) (fold-apply γ fm v a) (fold-apply γ' fm v a')
      fold-apply-resp γ≈ fbase        Fin.zero    {a} {a'} p = fold-idx-resp γ≈ {a} {a'} p
      fold-apply-resp γ≈ fbase        (Fin.suc i) p = p
      fold-apply-resp γ≈ (fbind Q fm) Fin.zero    {a} {a'} p = fold-reindex-resp {Q = Q} γ≈ fm {a} {a'} p
      fold-apply-resp γ≈ (fbind Q fm) (Fin.suc v) p = fold-apply-resp γ≈ fm v p

    -- The fibre fold: collapse the tree's fibre via `alg.famf`, threading the Γ-fibre.
    mutual
      fold-fam : (γ : Γ .idx .Carrier) (t : Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
                 prod (Γ .fam .fm γ) (Tδ.fib P (λ i → lift tt) t) ⇒ A .fam .fm (fold-idx γ t)
      fold-fam γ (Tδ.sup x) =
        alg .famf ._⇒f_.transf (γ , fold-shape-idx P γ x) ∘ pair p₁ (fold-shape-fam P γ x)

      fold-shape-fam : (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Srt.η₀ ∣ P ∣)) →
                       prod (Γ .fam .fm γ) (Tδ.fib-shape Q (Tδ.deco-ext P (λ i → lift tt)) x)
                         ⇒ fobj μ-fam Q (extend δ A) .fam .fm (fold-shape-idx Q γ x)
      fold-shape-fam (const A')        γ a = p₂
      fold-shape-fam (var Fin.zero)    γ t = fold-fam γ t
      fold-shape-fam (var (Fin.suc i)) γ a = p₂
      fold-shape-fam (Q₁ + Q₂) γ (inj₁ x) = under-root (fold-shape-fam Q₁ γ x)
      fold-shape-fam (Q₁ + Q₂) γ (inj₂ y) = under-root (fold-shape-fam Q₂ γ y)
      fold-shape-fam (Q₁ × Q₂) γ (x , y) =
        under-root (strong-prod-m (fold-shape-fam Q₁ γ x) (fold-shape-fam Q₂ γ y))
      fold-shape-fam (μ Q')    γ t = fold-reindex-fam {Q = Q'} γ fbase t

      fold-reindex-fam : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (t : Tδ.W ∣ Q ∣ ρ) →
                         prod (Γ .fam .fm γ) (Tδ.fib Q d t) ⇒ TA'.fib Q d' (fold-reindex γ md t)
      fold-reindex-fam {Q = Q} γ md (Tδ.sup x) = fold-reindex-shape-fam γ Q (fbind Q md) x

      fold-reindex-shape-fam : ∀ {j} (γ : Γ .idx .Carrier) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB) (a : Tδ.⟦ ∣ R ∣ ⟧shape ηA) →
                               prod (Γ .fam .fm γ) (Tδ.fib-shape R dA a) ⇒ TA'.fib-shape R dB (fold-reindex-shape γ R md a)
      fold-reindex-shape-fam γ (const A') md a = p₂
      fold-reindex-shape-fam γ (var v)    md a = fold-apply-fam γ md v a
      fold-reindex-shape-fam γ (P' + Q') md (inj₁ a) = under-root (fold-reindex-shape-fam γ P' md a)
      fold-reindex-shape-fam γ (P' + Q') md (inj₂ b) = under-root (fold-reindex-shape-fam γ Q' md b)
      fold-reindex-shape-fam γ (P' × Q') md (a , b) =
        under-root (strong-prod-m (fold-reindex-shape-fam γ P' md a) (fold-reindex-shape-fam γ Q' md b))
      fold-reindex-shape-fam γ (μ Q'')   md t = fold-reindex-fam {Q = Q''} γ md t

      fold-apply-fam : ∀ {k} {ρ ρ' d d'} (γ : Γ .idx .Carrier) (md : FMor ρ ρ' d d') (v : Fin k) (a : Tδ.El (ρ v)) →
                       prod (Γ .fam .fm γ) (Tδ.fib-el (ρ v) (d v) a) ⇒ TA'.fib-el (ρ' v) (d' v) (fold-apply γ md v a)
      fold-apply-fam γ fbase        Fin.zero    t = fold-fam γ t
      fold-apply-fam γ fbase        (Fin.suc i) a = p₂
      fold-apply-fam γ (fbind Q md) Fin.zero    a = fold-reindex-fam {Q = Q} γ md a
      fold-apply-fam γ (fbind Q md) (Fin.suc v) a = fold-apply-fam γ md v a

    -- The fibre fold is natural: it commutes with `subst` (in both Γ and the tree).
    mutual
      fold-fam-natural : ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {t t'} (p : Tδ.W-≈ t t') →
                         fold-fam γ₂ t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst P (λ i → lift tt) {x = t} {y = t'} p) ≈
                         A .fam .subst (fold-idx-resp γ≈ {t} {t'} p) ∘ fold-fam γ₁ t
      fold-fam-natural {γ₁} {γ₂} γ≈ {Tδ.sup x} {Tδ.sup y} p =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl (pair-natural _ _ _))
        (≈-trans (∘-cong ≈-refl (pair-cong (pair-p₁ _ _) (fold-shape-fam-natural P γ≈ {x} {y} p)))
        (≈-trans (∘-cong ≈-refl (≈-sym (pair-compose _ _ _ _)))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong (alg .famf ._⇒f_.natural (γ≈ , fold-shape-idx-resp P γ≈ {x} {y} p)) ≈-refl)
                 (assoc _ _ _))))))

      fold-shape-fam-natural : (Q : Poly (suc n)) → ∀ {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) {x x'}
                               (p : Tδ.shape≈ ∣ Q ∣ (Srt.η₀ ∣ P ∣) x x') →
                               fold-shape-fam Q γ₂ x' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst Q (Tδ.deco-ext P (λ i → lift tt)) p) ≈
                               fobj μ-fam Q (extend δ A) .fam .subst (fold-shape-idx-resp Q γ≈ p) ∘ fold-shape-fam Q γ₁ x
      fold-shape-fam-natural (const A')        γ≈ p = pair-p₂ _ _
      fold-shape-fam-natural (var Fin.zero)    γ≈ {x} {x'} p = fold-fam-natural γ≈ {x} {x'} p
      fold-shape-fam-natural (var (Fin.suc i)) γ≈ p = pair-p₂ _ _
      fold-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₁ x} {inj₁ x'} p =
        under-root-natural (Γ .fam .subst γ≈)
          (Tδ.fib-shape-subst Q₁ (Tδ.deco-ext P (λ i → lift tt)) p)
          (fobj μ-fam Q₁ (extend δ A) .fam .subst (fold-shape-idx-resp Q₁ γ≈ p))
          (fold-shape-fam Q₁ γ₁ x) (fold-shape-fam Q₁ γ₂ x')
          (fold-shape-fam-natural Q₁ γ≈ p)
      fold-shape-fam-natural (Q₁ + Q₂) {γ₁} {γ₂} γ≈ {inj₂ y} {inj₂ y'} p =
        under-root-natural (Γ .fam .subst γ≈)
          (Tδ.fib-shape-subst Q₂ (Tδ.deco-ext P (λ i → lift tt)) p)
          (fobj μ-fam Q₂ (extend δ A) .fam .subst (fold-shape-idx-resp Q₂ γ≈ p))
          (fold-shape-fam Q₂ γ₁ y) (fold-shape-fam Q₂ γ₂ y')
          (fold-shape-fam-natural Q₂ γ≈ p)
      fold-shape-fam-natural (Q₁ × Q₂) {γ₁} {γ₂} γ≈ {x₁ , x₂} {x₁' , x₂'} (p₁p , p₂p) =
        under-root-natural (Γ .fam .subst γ≈)
          (prod-m (Tδ.fib-shape-subst Q₁ (Tδ.deco-ext P (λ i → lift tt)) p₁p)
                  (Tδ.fib-shape-subst Q₂ (Tδ.deco-ext P (λ i → lift tt)) p₂p))
          (prod-m (fobj μ-fam Q₁ (extend δ A) .fam .subst (fold-shape-idx-resp Q₁ γ≈ p₁p))
                  (fobj μ-fam Q₂ (extend δ A) .fam .subst (fold-shape-idx-resp Q₂ γ≈ p₂p)))
          (strong-prod-m (fold-shape-fam Q₁ γ₁ x₁) (fold-shape-fam Q₂ γ₁ x₂))
          (strong-prod-m (fold-shape-fam Q₁ γ₂ x₁') (fold-shape-fam Q₂ γ₂ x₂'))
          (strong-prod-m-natural (fold-shape-fam-natural Q₁ γ≈ p₁p) (fold-shape-fam-natural Q₂ γ≈ p₂p))
      fold-shape-fam-natural (μ Q')    γ≈ {x} {x'} p = fold-reindex-fam-natural {Q = Q'} γ≈ fbase {x} {x'} p

      fold-reindex-fam-natural : ∀ {k} {Q : Poly (suc k)} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂)
                             (md : FMor ρ ρ' d d') {t t' : Tδ.W ∣ Q ∣ ρ} (p : Tδ.W-≈ t t') →
                             (fold-reindex-fam γ₂ md t' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-subst Q d {x = t} {y = t'} p))
                               ≈ (TA'.fib-subst Q d' {x = fold-reindex γ₁ md t} {y = fold-reindex γ₂ md t'}
                                                (fold-reindex-resp γ≈ md {t} {t'} p) ∘ fold-reindex-fam γ₁ md t)
      fold-reindex-fam-natural {Q = Q} γ≈ md {Tδ.sup x} {Tδ.sup y} p = fold-reindex-shape-fam-natural γ≈ Q (fbind Q md) {x} {y} p

      fold-reindex-shape-fam-natural : ∀ {j} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (R : Poly j) {ηA ηB dA dB} (md : FMor ηA ηB dA dB)
                                   {a a' : Tδ.⟦ ∣ R ∣ ⟧shape ηA} (p : Tδ.shape≈ ∣ R ∣ ηA a a') →
                                   (fold-reindex-shape-fam γ₂ R md a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-shape-subst R dA p))
                                     ≈ (TA'.fib-shape-subst R dB (fold-reindex-shape-resp γ≈ R md p) ∘ fold-reindex-shape-fam γ₁ R md a)
      fold-reindex-shape-fam-natural γ≈ (const A') md p = pair-p₂ _ _
      fold-reindex-shape-fam-natural γ≈ (var v)    md p = fold-apply-fam-natural γ≈ md v p
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₁ a} {inj₁ a'} p =
        under-root-natural (Γ .fam .subst γ≈)
          (Tδ.fib-shape-subst P' dA p)
          (TA'.fib-shape-subst P' dB (fold-reindex-shape-resp γ≈ P' md p))
          (fold-reindex-shape-fam γ₁ P' md a) (fold-reindex-shape-fam γ₂ P' md a')
          (fold-reindex-shape-fam-natural γ≈ P' md p)
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' + Q') {dA = dA} {dB} md {inj₂ b} {inj₂ b'} p =
        under-root-natural (Γ .fam .subst γ≈)
          (Tδ.fib-shape-subst Q' dA p)
          (TA'.fib-shape-subst Q' dB (fold-reindex-shape-resp γ≈ Q' md p))
          (fold-reindex-shape-fam γ₁ Q' md b) (fold-reindex-shape-fam γ₂ Q' md b')
          (fold-reindex-shape-fam-natural γ≈ Q' md p)
      fold-reindex-shape-fam-natural {γ₁ = γ₁} {γ₂} γ≈ (P' × Q') {dA = dA} {dB} md {a₁ , a₂} {a₁' , a₂'} (p₁p , p₂p) =
        under-root-natural (Γ .fam .subst γ≈)
          (prod-m (Tδ.fib-shape-subst P' dA p₁p) (Tδ.fib-shape-subst Q' dA p₂p))
          (prod-m (TA'.fib-shape-subst P' dB (fold-reindex-shape-resp γ≈ P' md p₁p))
                  (TA'.fib-shape-subst Q' dB (fold-reindex-shape-resp γ≈ Q' md p₂p)))
          (strong-prod-m (fold-reindex-shape-fam γ₁ P' md a₁) (fold-reindex-shape-fam γ₁ Q' md a₂))
          (strong-prod-m (fold-reindex-shape-fam γ₂ P' md a₁') (fold-reindex-shape-fam γ₂ Q' md a₂'))
          (strong-prod-m-natural (fold-reindex-shape-fam-natural γ≈ P' md p₁p)
                                 (fold-reindex-shape-fam-natural γ≈ Q' md p₂p))
      fold-reindex-shape-fam-natural γ≈ (μ Q'')   md {a} {a'} p = fold-reindex-fam-natural {Q = Q''} γ≈ md {a} {a'} p

      fold-apply-fam-natural : ∀ {k} {ρ ρ' d d'} {γ₁ γ₂} (γ≈ : _≈s_ (Γ .idx) γ₁ γ₂) (md : FMor ρ ρ' d d') (v : Fin k)
                               {a a'} (p : Tδ.elEq (ρ v) a a') →
                               fold-apply-fam γ₂ md v a' ∘ prod-m (Γ .fam .subst γ≈) (Tδ.fib-el-subst (ρ v) (d v) p) ≈
                               TA'.fib-el-subst (ρ' v) (d' v) (fold-apply-resp γ≈ md v p) ∘ fold-apply-fam γ₁ md v a
      fold-apply-fam-natural γ≈ fbase        Fin.zero    {a} {a'} p = fold-fam-natural γ≈ {a} {a'} p
      fold-apply-fam-natural γ≈ fbase        (Fin.suc i) p = pair-p₂ _ _
      fold-apply-fam-natural γ≈ (fbind Q md) Fin.zero    {a} {a'} p = fold-reindex-fam-natural {Q = Q} γ≈ md {a} {a'} p
      fold-apply-fam-natural γ≈ (fbind Q md) (Fin.suc v) p = fold-apply-fam-natural γ≈ md v p

    foldMor : Mor (Fam𝒞-P.prod Γ (μ-fam P δ)) A
    foldMor .idxf .PS._⇒_.func (γ , t) = fold-idx γ t
    foldMor .idxf .PS._⇒_.func-resp-≈ {γ , t} {γ' , t'} (γ≈ , t≈) = fold-idx-resp γ≈ {t} {t'} t≈
    foldMor .famf ._⇒f_.transf (γ , t) = fold-fam γ t
    foldMor .famf ._⇒f_.natural {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) = fold-fam-natural γ≈ {t₁} {t₂} t≈
