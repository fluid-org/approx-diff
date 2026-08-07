{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Reflection, fibre half: applying the intro algebra at the projection
-- candidate is the projection, so the projection is the fold of the intro
-- algebra. The apply-morphisms are undone by the bridge reindex on one side
-- and matched by the inverse bridge on the other, so each transport across the
-- lifting fuses at an isomorphism assembled from the Lambek round trips.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import prop using (_,_)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import lifting using (Lifting)
open import prop-setoid as PS using ()
open import indexed-family using (_⇒f_)
import fam-mu-lifting.laws
import fam-mu-lifting.lambek

module unused.fam-mu-lifting.reflection {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c) where

open fam-mu-lifting.laws os es T CM BP Lft public
private module Lk = fam-mu-lifting.lambek os es T CM BP Lft

-- The strong product action of two projections is the projection.
spm-p₂ : ∀ {w x₁ x₂} → strong-prod-m (p₂ {w} {x₁}) (p₂ {w} {x₂}) ≈ p₂
spm-p₂ = ≈-trans (pair-cong (pair-p₂ _ _) (pair-p₂ _ _)) (pair-ext _)

module ReflectionFam {n} {Γ : Obj} {P : Poly (suc n)} {δ : Fin n → Obj} where
  private
    module At = InMapDef P δ
    module Rf = Reflection {n} {Γ} {P} {δ}
    module Lb = Lk.LambekDef P δ
    module R' = Reindex δ (extend δ (μObj P δ))
  open FoldBase {n} {Γ} {μObj P δ} {P} {δ}

  -- Pair each fold-reindex morphism with the bridge that undoes it and the inverse bridge that
  -- matches it.
  data TRel : ∀ {j} {ρ : Fin j → Fin n ⊎ Sort n} {ρ' : Fin j → Fin (suc n) ⊎ Sort (suc n)}
              {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → TA'.DecoAssign (ρ' v)} →
              FMor ρ ρ' d d' → R'.MorD ρ ρ' d d' → At.R.MorD ρ' ρ d' d →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    tbase : TRel fbase Lb.mor₀⁻ At.mor₀
    tbind : ∀ {j} {ρ ρ' d d'} {fm : FMor {j} ρ ρ' d d'} {md' md} (Q' : Poly (suc j)) →
            TRel fm md' md → TRel (fbind Q' fm) (R'.bind Q' md') (At.R.bind Q' md)

  trel-r : ∀ {j} {ρ ρ' d d'} {fm : FMor {j} ρ ρ' d d'} {md' md} → TRel fm md' md → Rf.RRel fm md
  trel-r tbase          = Rf.rbase
  trel-r (tbind Q' rel) = Rf.rbind Q' (trel-r rel)

  trel-d : ∀ {j} {ρ ρ' d d'} {fm : FMor {j} ρ ρ' d d'} {md' md} → TRel fm md' md → Lb.DRel md' md
  trel-d tbase          = Lb.dbase
  trel-d (tbind Q' rel) = Lb.dbind Q' (trel-d rel)

  -- At the projection candidate, applying agrees with the inverse bridge on indexes.
  mutual
    ar-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {fm : FMor ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
           (trel : TRel fm md' md) (γ : Γ .idx .Carrier) (t : Tδ.W ∣ Q̂ ∣ ρ) →
           TA'.W-≈ (R'.reindex md' t) (Rf.Ah.apply-reindex γ fm t)
    ar-W {Q̂ = Q̂} trel γ (Tδ.sup x) = ar-shape Q̂ (tbind Q̂ trel) γ x

    ar-shape : ∀ {j} (S : Poly j) {ρ ρ' d d'} {fm : FMor ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
               (trel : TRel fm md' md) (γ : Γ .idx .Carrier) (a : Tδ.⟦ ∣ S ∣ ⟧shape ρ) →
               TA'.shape≈ ∣ S ∣ ρ' (R'.reindex-shape ∣ S ∣ md' a) (Rf.Ah.apply-reindex-shape γ S fm a)
    ar-shape (const A') trel γ a = A' .idx .isEquivalence .refl
    ar-shape (var v)    trel γ a = ar-el trel γ v a
    ar-shape (P' + Q') trel γ (inj₁ a) = ar-shape P' trel γ a
    ar-shape (P' + Q') trel γ (inj₂ b) = ar-shape Q' trel γ b
    ar-shape (P' × Q') trel γ (a , b) = ar-shape P' trel γ a , ar-shape Q' trel γ b
    ar-shape (μ Q'')   trel γ t = ar-W {Q̂ = Q''} trel γ t

    ar-el : ∀ {j} {ρ ρ' d d'} {fm : FMor {j} ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
            (trel : TRel fm md' md) (γ : Γ .idx .Carrier) (v : Fin j) (a : Tδ.El (ρ v)) →
            TA'.elEq (ρ' v) (R'.apply md' v a) (Rf.Ah.apply-apply γ fm v a)
    ar-el tbase           γ Fin.zero    t = TA'.elEq-refl (inj₁ Fin.zero) t
    ar-el tbase           γ (Fin.suc i) a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
    ar-el (tbind Q' trel) γ Fin.zero    a = ar-W {Q̂ = Q'} trel γ a
    ar-el (tbind Q' trel) γ (Fin.suc v) a = ar-el trel γ v a

  -- The transported bridge reindex out of an applied fibre is an isomorphism, with the transported
  -- inverse bridge as inverse: both composites reduce to the Lambek round trips by naturality.
  iso-A : ∀ {j} (S : Poly j) {ρ ρ' d d'} {fm : FMor ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
          (trel : TRel fm md' md) (γ : Γ .idx .Carrier) (a : Tδ.⟦ ∣ S ∣ ⟧shape ρ) →
          ((Tδ.fib-shape-subst S d (Rf.ra-shape S (trel-r trel) γ a)
             ∘ At.R.reindex-fam S md {a = Rf.Ah.apply-reindex-shape γ S fm a})
           ∘ (TA'.fib-shape-subst S d' (ar-shape S trel γ a) ∘ R'.reindex-fam S md' {a = a}))
          ≈ id (Tδ.fib-shape S d a)
  iso-A S {d = d} trel γ a =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (≈-sym (assoc _ _ _)))
    (≈-trans (∘-cong₂ (∘-cong₁ (At.R.reindex-fam-natural S _ (ar-shape S trel γ a))))
    (≈-trans (∘-cong₂ (assoc _ _ _))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (≈-sym (Tδ.fib-shape-trans* S d
               (Rf.ra-shape S (trel-r trel) γ a)
               (At.R.reindex-shape-resp ∣ S ∣ _ (ar-shape S trel γ a)))))
             (Lb.drt-shape-fam S (trel-d trel) a))))))

  iso-B : ∀ {j} (S : Poly j) {ρ ρ' d d'} {fm : FMor ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
          (trel : TRel fm md' md) (γ : Γ .idx .Carrier) (a : Tδ.⟦ ∣ S ∣ ⟧shape ρ) →
          ((TA'.fib-shape-subst S d' (ar-shape S trel γ a) ∘ R'.reindex-fam S md' {a = a})
           ∘ (Tδ.fib-shape-subst S d (Rf.ra-shape S (trel-r trel) γ a)
              ∘ At.R.reindex-fam S md {a = Rf.Ah.apply-reindex-shape γ S fm a}))
          ≈ id (TA'.fib-shape S d' (Rf.Ah.apply-reindex-shape γ S fm a))
  iso-B S {d' = d'} {fm = fm} trel γ a =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (≈-sym (assoc _ _ _)))
    (≈-trans (∘-cong₂ (∘-cong₁ (R'.reindex-fam-natural S _ (Rf.ra-shape S (trel-r trel) γ a))))
    (≈-trans (∘-cong₂ (assoc _ _ _))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (≈-sym (TA'.fib-shape-trans* S d'
               (ar-shape S trel γ a)
               (R'.reindex-shape-resp ∣ S ∣ _ (Rf.ra-shape S (trel-r trel) γ a)))))
             (Lb.drt'-shape-fam S (trel-d trel) (Rf.Ah.apply-reindex-shape γ S fm a)))))))

  -- The fibre round trip at the projection candidate: undoing the applied fibres is the
  -- projection, the roots re-crossing the lifting at the isomorphisms above.
  mutual
    rf-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {fm : FMor ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
           (trel : TRel fm md' md) (γ : Γ .idx .Carrier) (t : Tδ.W ∣ Q̂ ∣ ρ) →
           (Tδ.fib-subst Q̂ d {x = At.R.reindex md (Rf.Ah.apply-reindex γ fm t)} {y = t}
              (Rf.ra-W (trel-r trel) γ t)
             ∘ (At.R.reindex-fam-W md {t = Rf.Ah.apply-reindex γ fm t} ∘ Rf.Ah.apply-reindex-fam γ fm t))
             ≈ p₂
    rf-W {Q̂ = Q̂} trel γ (Tδ.sup x) = rf-shape Q̂ (tbind Q̂ trel) γ x

    rf-shape : ∀ {j} (S : Poly j) {ρ ρ' d d'} {fm : FMor ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
               (trel : TRel fm md' md) (γ : Γ .idx .Carrier) (a : Tδ.⟦ ∣ S ∣ ⟧shape ρ) →
               (Tδ.fib-shape-subst S d (Rf.ra-shape S (trel-r trel) γ a)
                 ∘ (At.R.reindex-fam S md {a = Rf.Ah.apply-reindex-shape γ S fm a}
                    ∘ Rf.Ah.apply-reindex-shape-fam γ S fm a))
                 ≈ p₂
    rf-shape (const A') trel γ a =
      ≈-trans (∘-cong (A' .fam .refl*) id-left) id-left
    rf-shape (var v) trel γ a = rf-el trel γ v a
    rf-shape (P' + Q') trel γ (inj₁ a) =
      ≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong₁ (≈-sym (Lmap-comp _ _)))
      (≈-trans (under-root-post (iso-A P' trel γ a) (iso-B P' trel γ a) _)
      (≈-trans (under-root-cong (≈-trans (assoc _ _ _) (rf-shape P' trel γ a)))
               under-root-p₂)))
    rf-shape (P' + Q') trel γ (inj₂ b) =
      ≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong₁ (≈-sym (Lmap-comp _ _)))
      (≈-trans (under-root-post (iso-A Q' trel γ b) (iso-B Q' trel γ b) _)
      (≈-trans (under-root-cong (≈-trans (assoc _ _ _) (rf-shape Q' trel γ b)))
               under-root-p₂)))
    rf-shape (P' × Q') trel γ (a , b) =
      ≈-trans (≈-sym (assoc _ _ _))
      (≈-trans (∘-cong₁ (≈-trans (≈-sym (Lmap-comp _ _)) (Lmap-cong (≈-sym (prod-m-comp _ _ _ _)))))
      (≈-trans (under-root-post (pm-iso (iso-A P' trel γ a) (iso-A Q' trel γ b))
                                (pm-iso (iso-B P' trel γ a) (iso-B Q' trel γ b)) _)
      (≈-trans (under-root-cong
                 (≈-trans (strong-prod-m-post _ _ _ _)
                 (≈-trans (strong-prod-m-cong (≈-trans (assoc _ _ _) (rf-shape P' trel γ a))
                                              (≈-trans (assoc _ _ _) (rf-shape Q' trel γ b)))
                          spm-p₂)))
               under-root-p₂)))
    rf-shape (μ Q'') trel γ t = rf-W {Q̂ = Q''} trel γ t

    rf-el : ∀ {j} {ρ ρ' d d'} {fm : FMor {j} ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
            (trel : TRel fm md' md) (γ : Γ .idx .Carrier) (v : Fin j) (a : Tδ.El (ρ v)) →
            (Tδ.fib-el-subst (ρ v) (d v) (Rf.ra-el (trel-r trel) γ v a)
              ∘ (At.R.apply-fam md v (Rf.Ah.apply-apply γ fm v a) ∘ Rf.Ah.apply-apply-fam γ fm v a))
              ≈ p₂
    rf-el tbase γ Fin.zero t =
      ≈-trans (∘-cong (Tδ.fib-el-refl* (Sh.η₀ ∣ P ∣ Fin.zero)
                        (Tδ.deco-ext P (λ i → lift tt) Fin.zero) t)
                      id-left)
              id-left
    rf-el tbase γ (Fin.suc i) a =
      ≈-trans (∘-cong (Tδ.fib-el-refl* (Sh.η₀ ∣ P ∣ (Fin.suc i))
                        (Tδ.deco-ext P {ρ̄ = λ v → inj₁ v} (λ _ → lift tt) (Fin.suc i)) a)
                      id-left)
              id-left
    rf-el (tbind Q' trel) γ Fin.zero    a = rf-W {Q̂ = Q'} trel γ a
    rf-el (tbind Q' trel) γ (Fin.suc v) a = rf-el trel γ v a

  -- The top-level agreement through the embed bridge, and the top-level isomorphism.
  ar-top : ∀ (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
           TA'.shape≈ ∣ Q ∣ (λ v → inj₁ v)
             (R'.reindex-shape ∣ Q ∣ Lb.mor₀⁻ x) (At.embed-idx Q (Rf.Ah.apply-shape-idx Q γ x))
  ar-top (const A')        γ a = A' .idx .isEquivalence .refl
  ar-top (var Fin.zero)    γ t = TA'.elEq-refl (inj₁ Fin.zero) t
  ar-top (var (Fin.suc i)) γ a = TA'.elEq-refl (inj₁ (Fin.suc i)) a
  ar-top (Q₁ + Q₂) γ (inj₁ x) = ar-top Q₁ γ x
  ar-top (Q₁ + Q₂) γ (inj₂ y) = ar-top Q₂ γ y
  ar-top (Q₁ × Q₂) γ (x , y) = ar-top Q₁ γ x , ar-top Q₂ γ y
  ar-top (μ Q')    γ t = ar-W {Q̂ = Q'} tbase γ t

  top-A : ∀ (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
          ((Tδ.fib-shape-subst Q (Tδ.deco-ext P (λ i → lift tt)) (Rf.ra-top Q γ x)
             ∘ (At.R.reindex-fam Q At.mor₀ {a = At.embed-idx Q (Rf.Ah.apply-shape-idx Q γ x)}
                ∘ At.embed-fam Q (Rf.Ah.apply-shape-idx Q γ x)))
           ∘ ((fobj μObj Q At.δ' .fam .subst (At.unembed-embed Q (Rf.Ah.apply-shape-idx Q γ x))
               ∘ At.unembed-fam Q (At.embed-idx Q (Rf.Ah.apply-shape-idx Q γ x)))
              ∘ (TA'.fib-shape-subst Q (λ v → lift tt) (ar-top Q γ x)
                 ∘ R'.reindex-fam Q Lb.mor₀⁻ {a = x})))
          ≈ id (Tδ.fib-shape Q (Tδ.deco-ext P (λ i → lift tt)) x)
  top-A Q γ x =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (≈-trans (assoc _ _ _) (∘-cong₂ collapse-embed)))
    (≈-trans (∘-cong₂ (≈-sym (assoc _ _ _)))
    (≈-trans (∘-cong₂ (∘-cong₁ (At.R.reindex-fam-natural Q At.mor₀ (ar-top Q γ x))))
    (≈-trans (∘-cong₂ (assoc _ _ _))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (≈-sym (Tδ.fib-shape-trans* Q (Tδ.deco-ext P (λ i → lift tt))
               (Rf.ra-top Q γ x)
               (At.R.reindex-shape-resp ∣ Q ∣ At.mor₀ (ar-top Q γ x)))))
             (Lb.drt-shape-fam Q Lb.dbase x)))))))
    where
      collapse-embed =
        ≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (≈-sym (assoc _ _ _)))
        (≈-trans (∘-cong₁ (∘-cong₁ (At.embed-fam-natural Q
                   (At.unembed-embed Q (Rf.Ah.apply-shape-idx Q γ x)))))
        (≈-trans (∘-cong₁ (assoc _ _ _))
        (≈-trans (∘-cong₁ (At.embed-unembed-fam Q (At.embed-idx Q (Rf.Ah.apply-shape-idx Q γ x))))
                 id-left))))

  top-B : ∀ (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
          (((fobj μObj Q At.δ' .fam .subst (At.unembed-embed Q (Rf.Ah.apply-shape-idx Q γ x))
              ∘ At.unembed-fam Q (At.embed-idx Q (Rf.Ah.apply-shape-idx Q γ x)))
             ∘ (TA'.fib-shape-subst Q (λ v → lift tt) (ar-top Q γ x)
                ∘ R'.reindex-fam Q Lb.mor₀⁻ {a = x}))
           ∘ (Tδ.fib-shape-subst Q (Tδ.deco-ext P (λ i → lift tt)) (Rf.ra-top Q γ x)
              ∘ (At.R.reindex-fam Q At.mor₀ {a = At.embed-idx Q (Rf.Ah.apply-shape-idx Q γ x)}
                 ∘ At.embed-fam Q (Rf.Ah.apply-shape-idx Q γ x))))
          ≈ id (fobj μObj Q At.δ' .fam .fm (Rf.Ah.apply-shape-idx Q γ x))
  top-B Q γ x =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ collapse-trip)
    (≈-trans (assoc _ _ _)
             (At.unembed-embed-fam Q (Rf.Ah.apply-shape-idx Q γ x))))
    where
      collapse-trip =
        ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (≈-sym (assoc _ _ _)))
        (≈-trans (∘-cong₂ (∘-cong₁ (R'.reindex-fam-natural Q Lb.mor₀⁻ (Rf.ra-top Q γ x))))
        (≈-trans (∘-cong₂ (assoc _ _ _))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (≈-sym (TA'.fib-shape-trans* Q (λ v → lift tt)
                   (ar-top Q γ x)
                   (R'.reindex-shape-resp ∣ Q ∣ Lb.mor₀⁻ (Rf.ra-top Q γ x)))))
        (≈-trans (∘-cong₂ (≈-sym (assoc _ _ _)))
        (≈-trans (≈-sym (assoc _ _ _))
        (≈-trans (∘-cong₁ (Lb.drt'-shape-fam Q Lb.dbase
                   (At.embed-idx Q (Rf.Ah.apply-shape-idx Q γ x))))
                 id-left))))))))

  -- The top-level fibre round trip, through the embed bridge.
  rf-top : ∀ (Q : Poly (suc n)) (γ : Γ .idx .Carrier) (x : Tδ.⟦ ∣ Q ∣ ⟧shape (Sh.η₀ ∣ P ∣)) →
           (Tδ.fib-shape-subst Q (Tδ.deco-ext P (λ i → lift tt)) (Rf.ra-top Q γ x)
             ∘ ((At.R.reindex-fam Q At.mor₀ {a = At.embed-idx Q (Rf.Ah.apply-shape-idx Q γ x)}
                 ∘ At.embed-fam Q (Rf.Ah.apply-shape-idx Q γ x))
                ∘ Rf.Ah.apply-shape-fam Q γ x))
             ≈ p₂
  rf-top (const A') γ a =
    ≈-trans (∘-cong (A' .fam .refl*) (≈-trans (∘-cong₁ id-left) id-left)) id-left
  rf-top (var Fin.zero) γ t =
    ≈-trans (∘-cong (Tδ.fib-el-refl* (Sh.η₀ ∣ P ∣ Fin.zero)
                      (Tδ.deco-ext P (λ i → lift tt) Fin.zero) t)
                    (≈-trans (∘-cong₁ id-left) id-left))
            id-left
  rf-top (var (Fin.suc i)) γ a =
    ≈-trans (∘-cong (Tδ.fib-el-refl* (Sh.η₀ ∣ P ∣ (Fin.suc i))
                      (Tδ.deco-ext P {ρ̄ = λ v → inj₁ v} (λ _ → lift tt) (Fin.suc i)) a)
                    (≈-trans (∘-cong₁ id-left) id-left))
            id-left
  rf-top (Q₁ + Q₂) γ (inj₁ x) =
    ≈-trans (∘-cong₂ (∘-cong₁ (≈-sym (Lmap-comp _ _))))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (≈-sym (Lmap-comp _ _)))
    (≈-trans (under-root-post (top-A Q₁ γ x) (top-B Q₁ γ x) _)
    (≈-trans (under-root-cong (≈-trans (assoc _ _ _) (rf-top Q₁ γ x)))
             under-root-p₂))))
  rf-top (Q₁ + Q₂) γ (inj₂ y) =
    ≈-trans (∘-cong₂ (∘-cong₁ (≈-sym (Lmap-comp _ _))))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (≈-sym (Lmap-comp _ _)))
    (≈-trans (under-root-post (top-A Q₂ γ y) (top-B Q₂ γ y) _)
    (≈-trans (under-root-cong (≈-trans (assoc _ _ _) (rf-top Q₂ γ y)))
             under-root-p₂))))
  rf-top (Q₁ × Q₂) γ (x , y) =
    ≈-trans (∘-cong₂ (∘-cong₁ (≈-trans (≈-sym (Lmap-comp _ _))
                                       (Lmap-cong (≈-sym (prod-m-comp _ _ _ _))))))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (≈-trans (≈-sym (Lmap-comp _ _)) (Lmap-cong (≈-sym (prod-m-comp _ _ _ _)))))
    (≈-trans (under-root-post (pm-iso (top-A Q₁ γ x) (top-A Q₂ γ y))
                              (pm-iso (top-B Q₁ γ x) (top-B Q₂ γ y)) _)
    (≈-trans (under-root-cong
               (≈-trans (strong-prod-m-post _ _ _ _)
               (≈-trans (strong-prod-m-cong (≈-trans (assoc _ _ _) (rf-top Q₁ γ x))
                                            (≈-trans (assoc _ _ _) (rf-top Q₂ γ y)))
                        spm-p₂)))
             under-root-p₂))))
  rf-top (μ Q') γ t =
    ≈-trans (∘-cong₂ (∘-cong₁ id-right)) (rf-W {Q̂ = Q'} tbase γ t)

  -- The projection satisfies the fused law at the intro algebra, so it is the fold.
  reflection : Rf.L'.IsFoldMor (Fam𝒞-P.p₂ {Γ} {μObj P δ})
  reflection .Rf.L'.IsFold.is-idx = Rf.reflection-idx
  reflection .Rf.L'.IsFold.is-fam γ x =
    ≈-sym (≈-trans (∘-cong₂ (∘-cong₁ id-left))
          (≈-trans (∘-cong₂ (assoc _ _ _))
          (≈-trans (∘-cong₂ (∘-cong₂ (pair-p₂ _ _)))
                   (rf-top P γ x))))

  reflection-fold : Fam𝒞-P.p₂ {Γ} {μObj P δ} ≃ FoldDef.foldMor {n} {Γ} {μObj P δ} {P} {δ} Rf.algR
  reflection-fold = Rf.L'.⦅⦆-η (Fam𝒞-P.p₂ {Γ} {μObj P δ}) reflection
