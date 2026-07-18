{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring; _⇒h_)
open import categories using (Category)
open import functor using (Functor)
import matrix
import matrix-functor
import matrix-embedding-semimod
import semimodule

-- Action of Mat(S) on the free semimodules X^ n, via the isomorphism of S with
-- the endomorphism semiring of 𝕀 and the embedding of matrices over the latter.
module matrix-semimod-action {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

private
  module S = CommutativeSemiring S
  module MES = matrix-embedding-semimod S
  module SemiMod = semimodule S
  module MS = matrix.Mat S
  module SM = Category SemiMod.cat

open MES using (X^; F)
open SemiMod using (𝕀)

mult-endo : S.Carrier → SemiMod._⇒_ 𝕀 𝕀
mult-endo s .SemiMod._⇒_.*→* .prop-setoid._⇒_.func y = y S.· s
mult-endo s .SemiMod._⇒_.*→* .prop-setoid._⇒_.func-resp-≈ e = S.·-cong e S.refl
mult-endo s .SemiMod._⇒_.preserve-ze = S.ε-annihilₗ
mult-endo s .SemiMod._⇒_.preserve-+ = S.·-+-distribᵣ
mult-endo s .SemiMod._⇒_.preserve-· = S.·-assoc

hom : S ⇒h MES.End𝕀
hom ._⇒h_.f = mult-endo
hom ._⇒h_.f-cong e .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' = S.·-cong y≈y' e
hom ._⇒h_.f-+ .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' =
  S.trans (S.·-cong y≈y' S.refl) S.·-+-distribₗ
hom ._⇒h_.f-· .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' =
  S.trans (S.·-cong y≈y' S.refl)
    (S.trans (S.·-cong S.refl S.·-comm) (S.sym (S.·-assoc)))
hom ._⇒h_.f-ε .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' =
  S.trans (S.·-cong y≈y' S.refl) S.ε-annihilᵣ
hom ._⇒h_.f-ι .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' =
  S.trans (S.·-cong y≈y' S.refl) (S.trans S.·-comm S.·-lunit)

private
  module EW = matrix-functor.Strict hom

mat-mor : ∀ {m n} → Category._⇒_ MS.cat m n → SM._⇒_ (X^ m) (X^ n)
mat-mor {m} {n} M = F .Functor.fmor {m} {n} (EW.E M)

mat-mor-cong : ∀ {m n} {M N : Category._⇒_ MS.cat m n} →
               Category._≈_ MS.cat M N → SM._≈_ (mat-mor M) (mat-mor N)
mat-mor-cong {m} {n} {M} {N} e =
  F .Functor.fmor-cong {m} {n} {EW.E M} {EW.E N} (EW.E-cong e)

mat-mor-id : ∀ {n} → SM._≈_ (mat-mor (Category.id MS.cat n)) (SM.id (X^ n))
mat-mor-id {n} =
  SM.≈-trans (F .Functor.fmor-cong {n} {n} {EW.E (Category.id MS.cat n)} {Category.id MES.Mat.cat n}
                (EW.E-I {n}))
             (F .Functor.fmor-id {n})

mat-mor-∘ : ∀ {m n k} (M : Category._⇒_ MS.cat n k) (N : Category._⇒_ MS.cat m n) →
            SM._≈_ (mat-mor (Category._∘_ MS.cat M N))
                   (SM._∘_ (mat-mor M) (mat-mor N))
mat-mor-∘ {m} {n} {k} M N =
  SM.≈-trans (F .Functor.fmor-cong {m} {k}
                {EW.E (Category._∘_ MS.cat M N)} {Category._∘_ MES.Mat.cat (EW.E M) (EW.E N)}
                (EW.E-∘ M N))
             (F .Functor.fmor-comp (EW.E M) (EW.E N))
