{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Lambek for the rooted μ-types, round trips: the fold-specific bridge
-- reindex has an inverse with identity fibres, and the two composites are the
-- identity on trees and on fibres. The relation extends the pairing across
-- binders, and the fibre composites fuse through the lifted action alone,
-- since reindexing carries no context.
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
open import lifting using (Lifting)
open import prop-setoid as PS using ()
open import indexed-family using (_⇒f_)
import fam-mu-lifting.in-map

module fam-mu-lifting.lambek {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CM : CMonEnriched 𝒞) (BP : ∀ x y → Biproduct CM x y)
    {𝟙c : Category.obj 𝒞} (Lft : Lifting CM 𝟙c) where

open fam-mu-lifting.in-map os es T CM BP Lft public

module LambekDef {n} (P : Poly (suc n)) (δ : Fin n → Obj) where
  private module At = InMapDef P δ
  open At using (module TX; module R; mor₀; m₀; embed-idx; unembed-idx)
  private
    module Tδ = Tree δ
    module R' = Reindex δ (extend δ (μObj P δ))

  -- The inverse bridge: the recursion slot and the parameters map to themselves.
  m₀⁻ : ∀ v → Tδ.El (Sh.η₀ ∣ P ∣ v) → TX.El (inj₁ v)
  m₀⁻ Fin.zero    a = a
  m₀⁻ (Fin.suc i) a = a

  m₀⁻-resp : ∀ v {a a'} → Tδ.elEq (Sh.η₀ ∣ P ∣ v) a a' → TX.elEq (inj₁ v) (m₀⁻ v a) (m₀⁻ v a')
  m₀⁻-resp Fin.zero    p = p
  m₀⁻-resp (Fin.suc i) p = p

  m₀⁻-fam : ∀ v (a : Tδ.El (Sh.η₀ ∣ P ∣ v)) →
            Tδ.fib-el (Sh.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v) a
              ⇒ TX.fib-el (inj₁ v) (lift tt) (m₀⁻ v a)
  m₀⁻-fam Fin.zero    a = id _
  m₀⁻-fam (Fin.suc i) a = id _

  m₀⁻-fam-natural : ∀ v {a a'} (p : Tδ.elEq (Sh.η₀ ∣ P ∣ v) a a') →
                    (m₀⁻-fam v a' ∘ Tδ.fib-el-subst (Sh.η₀ ∣ P ∣ v) (Tδ.deco-ext P (λ i → lift tt) v) p)
                      ≈ (TX.fib-el-subst (inj₁ v) (lift tt) (m₀⁻-resp v p) ∘ m₀⁻-fam v a)
  m₀⁻-fam-natural Fin.zero    p = ≈-trans id-left (≈-sym id-right)
  m₀⁻-fam-natural (Fin.suc i) p = ≈-trans id-left (≈-sym id-right)

  mor₀⁻ : R'.MorD (Sh.η₀ ∣ P ∣) (λ v → inj₁ v) (Tδ.deco-ext P (λ i → lift tt)) (λ v → lift tt)
  mor₀⁻ = R'.base m₀⁻ m₀⁻-resp m₀⁻-fam m₀⁻-fam-natural

  -- Pair each extension of the inverse bridge with the extension of the bridge it undoes.
  data DRel : ∀ {j} {ρ : Fin j → Fin n ⊎ Sort n} {ρ' : Fin j → Fin (suc n) ⊎ Sort (suc n)}
              {d : ∀ v → Tδ.DecoAssign (ρ v)} {d' : ∀ v → TX.DecoAssign (ρ' v)} →
              R'.MorD ρ ρ' d d' → R.MorD ρ' ρ d' d →
              Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
    dbase : DRel mor₀⁻ mor₀
    dbind : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md} (Q' : Poly (suc j)) →
            DRel md' md → DRel (R'.bind Q' md') (R.bind Q' md)

  -- Round trip on the parameter side: back and forth is the identity.
  mutual
    drt-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md} → DRel md' md →
            (t : Tδ.W ∣ Q̂ ∣ ρ) → Tδ.W-≈ (R.reindex md (R'.reindex md' t)) t
    drt-W {Q̂ = Q̂} rel (Tδ.sup x) = drt-shape Q̂ (dbind Q̂ rel) x

    drt-shape : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md} → DRel md' md →
                (a : Tδ.⟦ ∣ S ∣ ⟧shape ρ) →
                Tδ.shape≈ ∣ S ∣ ρ (R.reindex-shape ∣ S ∣ md (R'.reindex-shape ∣ S ∣ md' a)) a
    drt-shape (const A') rel a = A' .idx .isEquivalence .refl
    drt-shape (var v)    rel a = drt-el rel v a
    drt-shape (P' + Q') rel (inj₁ a) = drt-shape P' rel a
    drt-shape (P' + Q') rel (inj₂ b) = drt-shape Q' rel b
    drt-shape (P' × Q') rel (a , b) = drt-shape P' rel a , drt-shape Q' rel b
    drt-shape (μ Q'')   rel t = drt-W {Q̂ = Q''} rel t

    drt-el : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md} → DRel md' md →
             (v : Fin j) (a : Tδ.El (ρ v)) →
             Tδ.elEq (ρ v) (R.apply md v (R'.apply md' v a)) a
    drt-el dbase          Fin.zero    t = Tδ.elEq-refl (Sh.η₀ ∣ P ∣ Fin.zero) t
    drt-el dbase          (Fin.suc i) a = Tδ.elEq-refl (Sh.η₀ ∣ P ∣ (Fin.suc i)) a
    drt-el (dbind Q' rel) Fin.zero    a = drt-W {Q̂ = Q'} rel a
    drt-el (dbind Q' rel) (Fin.suc v) a = drt-el rel v a

  -- Round trip on the recursion side.
  mutual
    drt'-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md} → DRel md' md →
             (u : TX.W ∣ Q̂ ∣ ρ') → TX.W-≈ (R'.reindex md' (R.reindex md u)) u
    drt'-W {Q̂ = Q̂} rel (TX.sup x) = drt'-shape Q̂ (dbind Q̂ rel) x

    drt'-shape : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md} → DRel md' md →
                 (a : TX.⟦ ∣ S ∣ ⟧shape ρ') →
                 TX.shape≈ ∣ S ∣ ρ' (R'.reindex-shape ∣ S ∣ md' (R.reindex-shape ∣ S ∣ md a)) a
    drt'-shape (const A') rel a = A' .idx .isEquivalence .refl
    drt'-shape (var v)    rel a = drt'-el rel v a
    drt'-shape (P' + Q') rel (inj₁ a) = drt'-shape P' rel a
    drt'-shape (P' + Q') rel (inj₂ b) = drt'-shape Q' rel b
    drt'-shape (P' × Q') rel (a , b) = drt'-shape P' rel a , drt'-shape Q' rel b
    drt'-shape (μ Q'')   rel t = drt'-W {Q̂ = Q''} rel t

    drt'-el : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md} → DRel md' md →
              (v : Fin j) (a : TX.El (ρ' v)) →
              TX.elEq (ρ' v) (R'.apply md' v (R.apply md v a)) a
    drt'-el dbase          Fin.zero    t = TX.elEq-refl (inj₁ Fin.zero) t
    drt'-el dbase          (Fin.suc i) a = TX.elEq-refl (inj₁ (Fin.suc i)) a
    drt'-el (dbind Q' rel) Fin.zero    a = drt'-W {Q̂ = Q'} rel a
    drt'-el (dbind Q' rel) (Fin.suc v) a = drt'-el rel v a

  -- Fibre halves of the round trips: the fibre composites, transported along the index round
  -- trips, are the identity. Pure Lmap and prod-m algebra; no isomorphisms are needed.
  mutual
    drt-fam-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
                (rel : DRel md' md) (t : Tδ.W ∣ Q̂ ∣ ρ) →
                (Tδ.fib-subst Q̂ d {x = R.reindex md (R'.reindex md' t)} {y = t} (drt-W rel t)
                  ∘ (R.reindex-fam-W md {t = R'.reindex md' t} ∘ R'.reindex-fam-W md' {t = t}))
                  ≈ id (Tδ.fib Q̂ d t)
    drt-fam-W {Q̂ = Q̂} rel (Tδ.sup x) = drt-shape-fam Q̂ (dbind Q̂ rel) x

    drt-shape-fam : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
                    (rel : DRel md' md) (a : Tδ.⟦ ∣ S ∣ ⟧shape ρ) →
                    (Tδ.fib-shape-subst S d (drt-shape S rel a)
                      ∘ (R.reindex-fam S md {a = R'.reindex-shape ∣ S ∣ md' a} ∘ R'.reindex-fam S md' {a = a}))
                      ≈ id (Tδ.fib-shape S d a)
    drt-shape-fam (const A') rel a =
      ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    drt-shape-fam (var v) rel a = drt-el-fam rel v a
    drt-shape-fam (P' + Q') rel (inj₁ a) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (drt-shape-fam P' rel a)) Lmap-id))
    drt-shape-fam (P' + Q') rel (inj₂ b) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (drt-shape-fam Q' rel b)) Lmap-id))
    drt-shape-fam (P' × Q') rel (a , b) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
                     (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                       (≈-trans (prod-m-cong (drt-shape-fam P' rel a) (drt-shape-fam Q' rel b))
                                prod-m-id))))
                 Lmap-id))
    drt-shape-fam (μ Q'') rel t = drt-fam-W {Q̂ = Q''} rel t

    drt-el-fam : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md}
                 (rel : DRel md' md) (v : Fin j) (a : Tδ.El (ρ v)) →
                 (Tδ.fib-el-subst (ρ v) (d v) (drt-el rel v a)
                   ∘ (R.apply-fam md v (R'.apply md' v a) ∘ R'.apply-fam md' v a))
                   ≈ id (Tδ.fib-el (ρ v) (d v) a)
    drt-el-fam dbase Fin.zero t =
      ≈-trans (∘-cong (Tδ.fib-el-refl* (Sh.η₀ ∣ P ∣ Fin.zero) (Tδ.deco-ext P (λ i → lift tt) Fin.zero) t)
                      ≈-refl)
              (≈-trans id-left id-left)
    drt-el-fam dbase (Fin.suc i) a =
      ≈-trans (∘-cong (Tδ.fib-el-refl* (Sh.η₀ ∣ P ∣ (Fin.suc i))
                                       (Tδ.deco-ext P {ρ̄ = λ v → inj₁ v} (λ _ → lift tt) (Fin.suc i)) a)
                      ≈-refl)
              (≈-trans id-left id-left)
    drt-el-fam (dbind Q' rel) Fin.zero    a = drt-fam-W {Q̂ = Q'} rel a
    drt-el-fam (dbind Q' rel) (Fin.suc v) a = drt-el-fam rel v a

  mutual
    drt'-fam-W : ∀ {j} {Q̂ : Poly (suc j)} {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
                 (rel : DRel md' md) (u : TX.W ∣ Q̂ ∣ ρ') →
                 (TX.fib-subst Q̂ d' {x = R'.reindex md' (R.reindex md u)} {y = u} (drt'-W rel u)
                   ∘ (R'.reindex-fam-W md' {t = R.reindex md u} ∘ R.reindex-fam-W md {t = u}))
                   ≈ id (TX.fib Q̂ d' u)
    drt'-fam-W {Q̂ = Q̂} rel (TX.sup x) = drt'-shape-fam Q̂ (dbind Q̂ rel) x

    drt'-shape-fam : ∀ {j} (S : Poly j) {ρ ρ' d d'} {md' : R'.MorD ρ ρ' d d'} {md}
                     (rel : DRel md' md) (a : TX.⟦ ∣ S ∣ ⟧shape ρ') →
                     (TX.fib-shape-subst S d' (drt'-shape S rel a)
                       ∘ (R'.reindex-fam S md' {a = R.reindex-shape ∣ S ∣ md a} ∘ R.reindex-fam S md {a = a}))
                       ≈ id (TX.fib-shape S d' a)
    drt'-shape-fam (const A') rel a =
      ≈-trans (∘-cong (A' .fam .refl*) ≈-refl) (≈-trans id-left id-left)
    drt'-shape-fam (var v) rel a = drt'-el-fam rel v a
    drt'-shape-fam (P' + Q') rel (inj₁ a) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (drt'-shape-fam P' rel a)) Lmap-id))
    drt'-shape-fam (P' + Q') rel (inj₂ b) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong (drt'-shape-fam Q' rel b)) Lmap-id))
    drt'-shape-fam (P' × Q') rel (a , b) =
      ≈-trans (∘-cong ≈-refl (≈-sym (Lmap-comp _ _)))
      (≈-trans (≈-sym (Lmap-comp _ _))
        (≈-trans (Lmap-cong
                   (≈-trans (∘-cong ≈-refl (≈-sym (prod-m-comp _ _ _ _)))
                     (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                       (≈-trans (prod-m-cong (drt'-shape-fam P' rel a) (drt'-shape-fam Q' rel b))
                                prod-m-id))))
                 Lmap-id))
    drt'-shape-fam (μ Q'') rel t = drt'-fam-W {Q̂ = Q''} rel t

    drt'-el-fam : ∀ {j} {ρ ρ' d d'} {md' : R'.MorD {j} ρ ρ' d d'} {md}
                  (rel : DRel md' md) (v : Fin j) (a : TX.El (ρ' v)) →
                  (TX.fib-el-subst (ρ' v) (d' v) (drt'-el rel v a)
                    ∘ (R'.apply-fam md' v (R.apply md v a) ∘ R.apply-fam md v a))
                    ≈ id (TX.fib-el (ρ' v) (d' v) a)
    drt'-el-fam dbase Fin.zero t =
      ≈-trans (∘-cong (TX.fib-el-refl* (inj₁ Fin.zero) (lift tt) t) ≈-refl) (≈-trans id-left id-left)
    drt'-el-fam dbase (Fin.suc i) a =
      ≈-trans (∘-cong (TX.fib-el-refl* (inj₁ (Fin.suc i)) (lift tt) a) ≈-refl) (≈-trans id-left id-left)
    drt'-el-fam (dbind Q' rel) Fin.zero    a = drt'-fam-W {Q̂ = Q'} rel a
    drt'-el-fam (dbind Q' rel) (Fin.suc v) a = drt'-el-fam rel v a

  -- The inverse of inMor: strip the root, reindex back to the fresh context, unembed.
  u-idx : Tδ.W ∣ P ∣ (λ i → inj₁ i) → fobj μObj P At.δ' .idx .Carrier
  u-idx (Tδ.sup x) = unembed-idx P (R'.reindex-shape ∣ P ∣ mor₀⁻ x)

  u-resp : {t t' : Tδ.W ∣ P ∣ (λ i → inj₁ i)} → Tδ.W-≈ t t' →
           _≈s_ (fobj μObj P At.δ' .idx) (u-idx t) (u-idx t')
  u-resp {Tδ.sup x} {Tδ.sup y} p =
    At.unembed-idx-resp P (R'.reindex-shape-resp ∣ P ∣ mor₀⁻ p)

  u-fam : (t : Tδ.W ∣ P ∣ (λ i → inj₁ i)) →
          μObj P δ .fam .fm t ⇒ fobj μObj P At.δ' .fam .fm (u-idx t)
  u-fam (Tδ.sup x) =
    At.unembed-fam P (R'.reindex-shape ∣ P ∣ mor₀⁻ x) ∘ R'.reindex-fam P mor₀⁻ {a = x}

  unMor : Mor (μObj P δ) (fobj μObj P At.δ')
  unMor .idxf .PS._⇒_.func = u-idx
  unMor .idxf .PS._⇒_.func-resp-≈ {t} {t'} = u-resp {t} {t'}
  unMor .famf ._⇒f_.transf = u-fam
  unMor .famf ._⇒f_.natural {Tδ.sup x} {Tδ.sup y} e =
    ≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ (R'.reindex-fam-natural P mor₀⁻ e))
    (≈-trans (≈-sym (assoc _ _ _))
    (≈-trans (∘-cong₁ (At.unembed-fam-natural P (R'.reindex-shape-resp ∣ P ∣ mor₀⁻ e)))
             (assoc _ _ _))))

  -- The triangle identities: inMor is an isomorphism (Lambek), with unMor the inverse. The index
  -- halves compose the bridges' round trips with the reindex round trips; the fibre halves push
  -- the transports through the fibre actions by naturality and close with the fibre round trips.
  inMor-unMor : Fam𝒞._∘_ At.inMor unMor ≃ Fam𝒞.id (μObj P δ)
  inMor-unMor ._≃_.idxf-eq .PS._≃m_.func-eq {Tδ.sup x} {Tδ.sup y} e =
    Tδ.shape≈-trans ∣ P ∣ (Sh.η₀ ∣ P ∣)
      (Tδ.shape≈-trans ∣ P ∣ (Sh.η₀ ∣ P ∣)
        (R.reindex-shape-resp ∣ P ∣ mor₀ (At.embed-unembed P (R'.reindex-shape ∣ P ∣ mor₀⁻ x)))
        (drt-shape P dbase x))
      e
  inMor-unMor ._≃_.famf-eq .indexed-family._≃f_.transf-eq {Tδ.sup x} =
    ≈-trans (∘-cong (Tδ.fib-shape-trans* P (Tδ.deco-ext P {ρ̄ = λ v → inj₁ v} (λ _ → lift tt))
                       (drt-shape P dbase x)
                       (R.reindex-shape-resp ∣ P ∣ mor₀ (At.embed-unembed P z)))
                    id-left)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ step₂) (drt-shape-fam P dbase x)))
    where
      z = R'.reindex-shape ∣ P ∣ mor₀⁻ x

      step₃ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-sym (R.reindex-fam-natural P mor₀ (At.embed-unembed P z))))
                       (assoc _ _ _))
      step₄ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-trans (assoc _ _ _) (At.embed-unembed-fam P z)))
                       id-left)
      step₂ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ step₃)
              (≈-trans (assoc _ _ _)
                       (∘-cong₂ step₄)))

  unMor-inMor : Fam𝒞._∘_ unMor At.inMor ≃ Fam𝒞.id (fobj μObj P At.δ')
  unMor-inMor ._≃_.idxf-eq .PS._≃m_.func-eq {i} {i'} e =
    fobj μObj P At.δ' .idx .isEquivalence .trans
      (fobj μObj P At.δ' .idx .isEquivalence .trans
        (At.unembed-idx-resp P (drt'-shape P dbase (At.embed-idx P i)))
        (At.unembed-embed P i))
      e
  unMor-inMor ._≃_.famf-eq .indexed-family._≃f_.transf-eq {i} =
    ≈-trans (∘-cong (fobj μObj P At.δ' .fam .trans*
                       (At.unembed-embed P i)
                       (At.unembed-idx-resp P (drt'-shape P dbase (At.embed-idx P i))))
                    id-left)
    (≈-trans (assoc _ _ _)
    (≈-trans (∘-cong₂ step₂) (At.unembed-embed-fam P i)))
    where
      step₃ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-sym (At.unembed-fam-natural P (drt'-shape P dbase (At.embed-idx P i)))))
                       (assoc _ _ _))
      step₄ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (≈-trans (assoc _ _ _) (drt'-shape-fam P dbase (At.embed-idx P i))))
                       id-left)
      step₂ = ≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ step₃)
              (≈-trans (assoc _ _ _)
                       (∘-cong₂ step₄)))
