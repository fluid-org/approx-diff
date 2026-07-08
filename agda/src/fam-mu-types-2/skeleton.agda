{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The μ-carrier of a polynomial coincides with that of its constant-free
-- skeleton at the environment extended by the constants: a constant and a
-- variable bound to an equal environment entry contribute the same carrier
-- data, so the two W-types agree up to renaming of tree constructors.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
import Data.Fin as Fin
open Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_)
open import prop using () renaming (_,_ to _,ₚ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst-subst-sym; subst-sym-subst)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; subst to ≡-subst)
open import categories using (Category; HasTerminal; HasProducts)
open import prop-setoid using (Setoid)
import polynomial-functor-2
import fam-mu-types-2.carrier

module fam-mu-types-2.skeleton {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open fam-mu-types-2.carrier os es T P
open polynomial-functor-2 using (#c; skeleton; skeleton-go; consts; _++e_)

-- Fixed data for one instance of the lemma: an environment and a constant
-- block over the Fam category.
module Skeleton {n k : ℕ} (δ : Fin n → Obj) (cs : Fin k → Obj) where

  δ⁺ : Fin (n +ℕ k) → Obj
  δ⁺ = δ ++e cs

  module T₁ = Tree δ
  module T₂ = Tree δ⁺

  -- Relate source references (environment positions or sorts) to target ones:
  -- environment positions inject on the left; sorts relate recursively, with
  -- the constant block of the source polynomial pointing at the constant
  -- entries of the extended environment.
  mutual
    data RefRel : (Fin n ⊎ Sort n) → (Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      env : ∀ {p} → RefRel (inj₁ p) (inj₁ (p ↑ˡ k))
      srt : ∀ {s₁ s₂} → SortRel s₁ s₂ → RefRel (inj₂ s₁) (inj₂ s₂)

    data SortRel : Sort n → Sort (n +ℕ k) → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      mk : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
           (∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k))) →
           (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (∀ c → cs (ι c) ≡ consts Q c) →
           SortRel (mkSort Q ρ₁) (mkSort (skeleton-go Q ι) ρ₂)

  -- The forward tree map: rename constant leaves to their variable images.
  mutual
    wfwd : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
           (∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k))) →
           (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (∀ c → cs (ι c) ≡ consts Q c) →
           T₁.W Q ρ₁ → T₂.W (skeleton-go Q ι) ρ₂
    wfwd {j} Q ρ₁ ι ρ₂ vars fresh csok (T₁.sup x) =
      T₂.sup (shape-fwd Q (extend ρ₁ (inj₂ (mkSort Q ρ₁))) ι (extend ρ₂ (inj₂ (mkSort (skeleton-go Q ι) ρ₂)))
                (extend-vars Q ρ₁ ι ρ₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok x)

    -- The extended environments stay related when entering a binder.
    extend-vars : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
                  (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
                  (∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k))) →
                  (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                  (∀ c → cs (ι c) ≡ consts Q c) →
                  ∀ i → RefRel (extend ρ₁ (inj₂ (mkSort Q ρ₁)) i)
                               (extend ρ₂ (inj₂ (mkSort (skeleton-go Q ι) ρ₂)) (i ↑ˡ k))
    extend-vars Q ρ₁ ι ρ₂ vars fresh csok Fin.zero    = srt (mk Q ρ₁ ι ρ₂ vars fresh csok)
    extend-vars Q ρ₁ ι ρ₂ vars fresh csok (Fin.suc i) = vars i

    extend-fresh : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
                   (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
                   (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                   ∀ (c : Fin k) → extend ρ₂ (inj₂ (mkSort (skeleton-go Q ι) ρ₂)) (suc j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)
    extend-fresh Q ρ₁ ι ρ₂ fresh c = fresh c

    shape-fwd : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
                (∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k))) →
                (∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                (∀ c → cs (ι c) ≡ consts Q c) →
                T₁.⟦ Q ⟧shape η₁ → T₂.⟦ skeleton-go Q ι ⟧shape η₂
    shape-fwd {jv} (const A) η₁ ι η₂ vars fresh csok x =
      ≡-subst T₂.El (≡-sym (fresh (ι Fin.zero)))
        (≡-subst (λ B → B .idx .Carrier)
          (≡-sym (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero))) x)
    shape-fwd (var i)   η₁ ι η₂ vars fresh csok x = el-fwd (vars i) x
    shape-fwd (Q + R)   η₁ ι η₂ vars fresh csok (inj₁ x) =
      inj₁ (shape-fwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
              (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x)
    shape-fwd (Q + R)   η₁ ι η₂ vars fresh csok (inj₂ y) =
      inj₂ (shape-fwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
              (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y)
    shape-fwd (Q × R)   η₁ ι η₂ vars fresh csok (x , y) =
      shape-fwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
      , shape-fwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-fwd (μ Q')    η₁ ι η₂ vars fresh csok x = wfwd Q' η₁ ι η₂ vars fresh csok x

    -- References transport elements.
    el-fwd : ∀ {r₁ r₂} → RefRel r₁ r₂ → T₁.El r₁ → T₂.El r₂
    el-fwd (env {p}) x =
      ≡-subst (λ B → B .idx .Carrier) (≡-sym (cong [ δ , cs ]′ (splitAt-↑ˡ n p k))) x
    el-fwd (srt (mk Q ρ₁ ι ρ₂ vars fresh csok)) x = wfwd Q ρ₁ ι ρ₂ vars fresh csok x

  -- Casts commute with the setoid equalities, by identity elimination.
  private
    cast-≈ : ∀ {B B' : Obj} (e : B ≡ B') {x y : B .idx .Carrier} →
             B .idx ._≈s_ x y →
             B' .idx ._≈s_ (≡-subst (λ Z → Z .idx .Carrier) e x) (≡-subst (λ Z → Z .idx .Carrier) e y)
    cast-≈ ≡-refl p = p

    el-cast-≈ : ∀ {r r' : Fin (n +ℕ k) ⊎ Sort (n +ℕ k)} (e : r ≡ r') {x y : T₂.El r} →
                T₂.elEq r x y → T₂.elEq r' (≡-subst T₂.El e x) (≡-subst T₂.El e y)
    el-cast-≈ ≡-refl p = p

  -- The forward map preserves bisimilarity.
  mutual
    w≈-fwd : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
             (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
             (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k))) →
             (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
             (csok : ∀ c → cs (ι c) ≡ consts Q c) →
             {x y : T₁.W Q ρ₁} → T₁.W-≈ x y →
             T₂.W-≈ (wfwd Q ρ₁ ι ρ₂ vars fresh csok x) (wfwd Q ρ₁ ι ρ₂ vars fresh csok y)
    w≈-fwd Q ρ₁ ι ρ₂ vars fresh csok {T₁.sup x} {T₁.sup y} p =
      shape≈-fwd Q (extend ρ₁ (inj₂ (mkSort Q ρ₁))) ι (extend ρ₂ (inj₂ (mkSort (skeleton-go Q ι) ρ₂)))
        (extend-vars Q ρ₁ ι ρ₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok p

    shape≈-fwd : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                 (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
                 (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k))) →
                 (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                 (csok : ∀ c → cs (ι c) ≡ consts Q c) →
                 {x y : T₁.⟦ Q ⟧shape η₁} → T₁.shape≈ Q η₁ x y →
                 T₂.shape≈ (skeleton-go Q ι) η₂ (shape-fwd Q η₁ ι η₂ vars fresh csok x) (shape-fwd Q η₁ ι η₂ vars fresh csok y)
    shape≈-fwd {jv} (const A) η₁ ι η₂ vars fresh csok p =
      el-cast-≈ (≡-sym (fresh (ι Fin.zero)))
        (cast-≈ (≡-sym (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero))) p)
    shape≈-fwd (var i)   η₁ ι η₂ vars fresh csok p = elEq-fwd (vars i) p
    shape≈-fwd (Q + R)   η₁ ι η₂ vars fresh csok {inj₁ _} {inj₁ _} p =
      shape≈-fwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) p
    shape≈-fwd (Q + R)   η₁ ι η₂ vars fresh csok {inj₂ _} {inj₂ _} p =
      shape≈-fwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) p
    shape≈-fwd (Q × R)   η₁ ι η₂ vars fresh csok {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-fwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) p
      ,ₚ shape≈-fwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) q
    shape≈-fwd (μ Q')    η₁ ι η₂ vars fresh csok {x} {y} p =
      w≈-fwd Q' η₁ ι η₂ vars fresh csok {x} {y} p

    elEq-fwd : ∀ {r₁ r₂} (r : RefRel r₁ r₂) {x y : T₁.El r₁} →
               T₁.elEq r₁ x y → T₂.elEq r₂ (el-fwd r x) (el-fwd r y)
    elEq-fwd (env {p}) q =
      cast-≈ (≡-sym (cong [ δ , cs ]′ (splitAt-↑ˡ n p k))) q
    elEq-fwd (srt (mk Q ρ₁ ι ρ₂ vars fresh csok)) {x} {y} q =
      w≈-fwd Q ρ₁ ι ρ₂ vars fresh csok {x} {y} q

  -- The backward tree map: rename the fresh variable leaves back to constants.
  mutual
    wbwd : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
           (∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k))) →
           (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (∀ c → cs (ι c) ≡ consts Q c) →
           T₂.W (skeleton-go Q ι) ρ₂ → T₁.W Q ρ₁
    wbwd {j} Q ρ₁ ι ρ₂ vars fresh csok (T₂.sup x) =
      T₁.sup (shape-bwd Q (extend ρ₁ (inj₂ (mkSort Q ρ₁))) ι (extend ρ₂ (inj₂ (mkSort (skeleton-go Q ι) ρ₂)))
                (extend-vars Q ρ₁ ι ρ₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok x)

    shape-bwd : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
                (∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k))) →
                (∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                (∀ c → cs (ι c) ≡ consts Q c) →
                T₂.⟦ skeleton-go Q ι ⟧shape η₂ → T₁.⟦ Q ⟧shape η₁
    shape-bwd {jv} (const A) η₁ ι η₂ vars fresh csok x =
      ≡-subst (λ B → B .idx .Carrier)
        (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero))
        (≡-subst T₂.El (fresh (ι Fin.zero)) x)
    shape-bwd (var i)   η₁ ι η₂ vars fresh csok x = el-bwd (vars i) x
    shape-bwd (Q + R)   η₁ ι η₂ vars fresh csok (inj₁ x) =
      inj₁ (shape-bwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
              (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x)
    shape-bwd (Q + R)   η₁ ι η₂ vars fresh csok (inj₂ y) =
      inj₂ (shape-bwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
              (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y)
    shape-bwd (Q × R)   η₁ ι η₂ vars fresh csok (x , y) =
      shape-bwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
      , shape-bwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-bwd (μ Q')    η₁ ι η₂ vars fresh csok x = wbwd Q' η₁ ι η₂ vars fresh csok x

    el-bwd : ∀ {r₁ r₂} → RefRel r₁ r₂ → T₂.El r₂ → T₁.El r₁
    el-bwd (env {p}) x =
      ≡-subst (λ B → B .idx .Carrier) (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)) x
    el-bwd (srt (mk Q ρ₁ ι ρ₂ vars fresh csok)) x = wbwd Q ρ₁ ι ρ₂ vars fresh csok x

  -- Equal elements are setoid-equal.
  private
    obj-≡-to-≈ : ∀ {B : Obj} {x y : B .idx .Carrier} → x ≡ y → B .idx ._≈s_ x y
    obj-≡-to-≈ {B} {x} ≡-refl = B .idx .isEquivalence .refl

    ≡-to-≈₁ : ∀ {r} {x y : T₁.El r} → x ≡ y → T₁.elEq r x y
    ≡-to-≈₁ {r} {x} ≡-refl = T₁.elEq-refl r x

    ≡-to-≈₂ : ∀ {r} {x y : T₂.El r} → x ≡ y → T₂.elEq r x y
    ≡-to-≈₂ {r} {x} ≡-refl = T₂.elEq-refl r x

    Car : Obj → Set os
    Car B = B .idx .Carrier

  -- Round trips: the two maps are mutually inverse up to bisimilarity.
  mutual
    w-fb : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
           (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k))) →
           (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (csok : ∀ c → cs (ι c) ≡ consts Q c) →
           (x : T₁.W Q ρ₁) →
           T₁.W-≈ (wbwd Q ρ₁ ι ρ₂ vars fresh csok (wfwd Q ρ₁ ι ρ₂ vars fresh csok x)) x
    w-fb Q ρ₁ ι ρ₂ vars fresh csok (T₁.sup x) =
      shape-fb Q (extend ρ₁ (inj₂ (mkSort Q ρ₁))) ι (extend ρ₂ (inj₂ (mkSort (skeleton-go Q ι) ρ₂)))
        (extend-vars Q ρ₁ ι ρ₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok x

    shape-fb : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
               (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
               (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k))) →
               (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
               (csok : ∀ c → cs (ι c) ≡ consts Q c) →
               (x : T₁.⟦ Q ⟧shape η₁) →
               T₁.shape≈ Q η₁ (shape-bwd Q η₁ ι η₂ vars fresh csok (shape-fwd Q η₁ ι η₂ vars fresh csok x)) x
    shape-fb {jv} (const A) η₁ ι η₂ vars fresh csok x =
      obj-≡-to-≈ {B = A} (≡-trans (cong (≡-subst Car E) (subst-subst-sym {P = T₂.El} F)) (subst-subst-sym {P = Car} E))
      where
        E = ≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero)
        F = fresh (ι Fin.zero)
    shape-fb (var i)   η₁ ι η₂ vars fresh csok x = el-fb (vars i) x
    shape-fb (Q + R)   η₁ ι η₂ vars fresh csok (inj₁ x) =
      shape-fb Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
    shape-fb (Q + R)   η₁ ι η₂ vars fresh csok (inj₂ y) =
      shape-fb R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-fb (Q × R)   η₁ ι η₂ vars fresh csok (x , y) =
      shape-fb Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
      ,ₚ shape-fb R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-fb (μ Q')    η₁ ι η₂ vars fresh csok x = w-fb Q' η₁ ι η₂ vars fresh csok x

    el-fb : ∀ {r₁ r₂} (r : RefRel r₁ r₂) (x : T₁.El r₁) →
            T₁.elEq r₁ (el-bwd r (el-fwd r x)) x
    el-fb (env {p}) x = obj-≡-to-≈ {B = δ p} (subst-subst-sym {P = Car} (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)))
    el-fb (srt (mk Q ρ₁ ι ρ₂ vars fresh csok)) x = w-fb Q ρ₁ ι ρ₂ vars fresh csok x

  mutual
    w-bf : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
           (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k))) →
           (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (csok : ∀ c → cs (ι c) ≡ consts Q c) →
           (y : T₂.W (skeleton-go Q ι) ρ₂) →
           T₂.W-≈ (wfwd Q ρ₁ ι ρ₂ vars fresh csok (wbwd Q ρ₁ ι ρ₂ vars fresh csok y)) y
    w-bf Q ρ₁ ι ρ₂ vars fresh csok (T₂.sup y) =
      shape-bf Q (extend ρ₁ (inj₂ (mkSort Q ρ₁))) ι (extend ρ₂ (inj₂ (mkSort (skeleton-go Q ι) ρ₂)))
        (extend-vars Q ρ₁ ι ρ₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok y

    shape-bf : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
               (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
               (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k))) →
               (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
               (csok : ∀ c → cs (ι c) ≡ consts Q c) →
               (y : T₂.⟦ skeleton-go Q ι ⟧shape η₂) →
               T₂.shape≈ (skeleton-go Q ι) η₂ (shape-fwd Q η₁ ι η₂ vars fresh csok (shape-bwd Q η₁ ι η₂ vars fresh csok y)) y
    shape-bf {jv} (const A) η₁ ι η₂ vars fresh csok y =
      ≡-to-≈₂ {r = η₂ (jv ↑ʳ ι Fin.zero)} (≡-trans (cong (≡-subst T₂.El (≡-sym F)) (subst-sym-subst {P = Car} E)) (subst-sym-subst {P = T₂.El} F))
      where
        E = ≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero)
        F = fresh (ι Fin.zero)
    shape-bf (var i)   η₁ ι η₂ vars fresh csok y = el-bf (vars i) y
    shape-bf (Q + R)   η₁ ι η₂ vars fresh csok (inj₁ y) =
      shape-bf Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) y
    shape-bf (Q + R)   η₁ ι η₂ vars fresh csok (inj₂ y) =
      shape-bf R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-bf (Q × R)   η₁ ι η₂ vars fresh csok (x , y) =
      shape-bf Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
      ,ₚ shape-bf R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-bf (μ Q')    η₁ ι η₂ vars fresh csok y = w-bf Q' η₁ ι η₂ vars fresh csok y

    el-bf : ∀ {r₁ r₂} (r : RefRel r₁ r₂) (y : T₂.El r₂) →
            T₂.elEq r₂ (el-fwd r (el-bwd r y)) y
    el-bf (env {p}) y = obj-≡-to-≈ {B = δ⁺ (p ↑ˡ k)} (subst-sym-subst {P = Car} (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)))
    el-bf (srt (mk Q ρ₁ ι ρ₂ vars fresh csok)) y = w-bf Q ρ₁ ι ρ₂ vars fresh csok y
