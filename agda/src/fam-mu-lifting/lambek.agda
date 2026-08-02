{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Lambek for the rooted μ-types, round trips: the fold-specific bridge
-- reindex has an inverse with identity fibres, and the two composites are the
-- identity on trees and on fibres. The relation extends the pairing across
-- binders, and the fibre composites fuse through the lifted action alone,
-- since reindexing carries no context.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
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
