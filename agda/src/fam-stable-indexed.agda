{-# OPTIONS --prop --postfix-projections --safe #-}

open import Data.Product using (_,_; proj₁; proj₂)
open import prop using (∃ₚ; ∃ₛ; ⟪_⟫; _,_; tt)
open prop.∃ₚ using (fst; snd)
open import prop-setoid using (Setoid; IsEquivalence)
open import categories using (Category; setoid→category)
open import functor using (Functor)
open import fam using (module CategoryOfFamilies)
import stable-coproducts-indexed

-- Fam categories have stable set-indexed coproducts: pulling a coproduct
-- decomposition back along a morphism splits the source over the same index,
-- one summand per index. Stated at diagonal setoid levels (index equality at
-- the carrier level), which the intended instance (both levels 0ℓ) satisfies;
-- a summand's index set collects the source indices landing in that summand,
-- which requires the membership proof to sit at the carrier level.
module fam-stable-indexed {o m e os} (𝒞 : Category o m e) where

open CategoryOfFamilies os os 𝒞
open Obj
open Mor
open _≃_
open import prop-setoid using (_⇒_) renaming (module _⇒_ to _⇒s_; _≃m_ to _≈s_)
open _⇒s_
open _≈s_
open import indexed-family using (_⇒f_; _≃f_)
open _⇒f_
open _≃f_
open Setoid
open Category 𝒞 using ()
  renaming (_∘_ to _∘C_; id to idC; _≈_ to _≈C_;
            id-left to id-leftC; id-right to id-rightC;
            ≈-refl to ≈-reflC; ≈-sym to ≈-symC; ≈-trans to ≈-transC;
            assoc to assocC; ∘-cong to ∘-congC; ∘-cong₁ to ∘-cong₁C; ∘-cong₂ to ∘-cong₂C)
open Category cat using (Iso) renaming (_∘_ to _∘cat_; ≈-trans to ≃-transC; ≈-sym to ≃-symC)
open Iso
open Functor

module SI = stable-coproducts-indexed {𝒞 = cat} bigCoproducts
open SI using (IdxStable; IdxStableBits; ∐; inj)

fam-stable-indexed : IdxStable
fam-stable-indexed {S} {D} {x} {y} f g = record { E = E ; leg = leg ; h = h ; eq = eq }
  where
    -- Where each index of y lands in the coproduct ∐ S D.
    p : y .idx ⇒ (∐ S D) .idx
    p = Mor-∘ (f .bwd) g .idxf

    sOf : y .idx .Carrier → S .Carrier
    sOf i = proj₁ (p .func i)

    dOf : (i : y .idx .Carrier) → D .fobj (sOf i) .idx .Carrier
    dOf i = proj₂ (p .func i)

    pfam = Mor-∘ (f .bwd) g .famf

    -- The s-th summand of y: the indices of y landing in the s-th component.
    E : Functor (setoid→category S) cat
    E .fobj s .idx .Carrier = ∃ₛ (y .idx .Carrier) (λ i → S ._≈_ (sOf i) s)
    E .fobj s .idx ._≈_ (i , _) (j , _) = y .idx ._≈_ i j
    E .fobj s .idx .isEquivalence .IsEquivalence.refl = y .idx .isEquivalence .IsEquivalence.refl
    E .fobj s .idx .isEquivalence .IsEquivalence.sym e = y .idx .isEquivalence .IsEquivalence.sym e
    E .fobj s .idx .isEquivalence .IsEquivalence.trans e₁ e₂ = y .idx .isEquivalence .IsEquivalence.trans e₁ e₂
    E .fobj s .fam .indexed-family.Fam.fm (i , _) = y .fam .indexed-family.Fam.fm i
    E .fobj s .fam .indexed-family.Fam.subst {i , _} {j , _} e = y .fam .indexed-family.Fam.subst e
    E .fobj s .fam .indexed-family.Fam.refl* {i , _} = y .fam .indexed-family.Fam.refl*
    E .fobj s .fam .indexed-family.Fam.trans* {i , _} {j , _} {k , _} e₁ e₂ = y .fam .indexed-family.Fam.trans* e₁ e₂
    E .fmor ⟪ s≈s' ⟫ .idxf .func (i , pf) = i , S .trans pf s≈s'
    E .fmor ⟪ s≈s' ⟫ .idxf .func-resp-≈ {i , _} {j , _} i≈j = i≈j
    E .fmor ⟪ s≈s' ⟫ .famf .transf (i , _) = idC (y .fam .indexed-family.Fam.fm i)
    E .fmor ⟪ s≈s' ⟫ .famf .natural {i , _} {j , _} e = ≈-transC id-leftC (≈-symC id-rightC)
    E .fmor-cong _ .idxf-eq .func-eq i≈j = i≈j
    E .fmor-cong _ .famf-eq .transf-eq = ≈-transC id-rightC (y .fam .indexed-family.Fam.refl*)
    E .fmor-id .idxf-eq .func-eq i≈j = i≈j
    E .fmor-id .famf-eq .transf-eq = ≈-transC id-rightC (y .fam .indexed-family.Fam.refl*)
    E .fmor-comp _ _ .idxf-eq .func-eq i≈j = i≈j
    E .fmor-comp _ _ .famf-eq .transf-eq {i , _} = ≈-transC id-rightC (≈-transC (y .fam .indexed-family.Fam.refl*) (≈-symC (≈-transC id-leftC id-leftC)))

    -- Each summand of y maps into the corresponding summand of x, transporting
    -- the recorded landing to the target index s.
    leg : ∀ s → Mor (E .fobj s) (D .fobj s)
    leg s .idxf .func (i , pf) = D .fmor ⟪ pf ⟫ .idxf .func (dOf i)
    leg s .idxf .func-resp-≈ {i , pf} {j , pf'} i≈j =
      D .fobj s .idx .trans
        (D .fmor-cong {f₁ = ⟪ pf ⟫} {f₂ = ⟪ S .trans (p .func-resp-≈ i≈j .fst) pf' ⟫} tt
           .idxf-eq .func-eq (D .fobj (sOf i) .idx .refl))
        (D .fobj s .idx .trans
          (D .fmor-comp ⟪ pf' ⟫ ⟪ p .func-resp-≈ i≈j .fst ⟫ .idxf-eq .func-eq (D .fobj (sOf i) .idx .refl))
          (D .fmor ⟪ pf' ⟫ .idxf .func-resp-≈ (p .func-resp-≈ i≈j .snd)))
    leg s .famf .transf (i , pf) =
      D .fmor ⟪ pf ⟫ .famf .transf (dOf i) ∘C pfam .transf i
    leg s .famf .natural {i , pf} {j , pf'} i≈j =
      ≈-transC (assocC _ _ _)
        (≈-transC (∘-cong₂C (pfam .natural i≈j))
          (≈-transC (≈-symC (assocC _ _ _))
            (≈-transC (∘-cong₁C core)
              (assocC _ _ _))))
      where
        e₀ : S ._≈_ (sOf i) (sOf j)
        e₀ = p .func-resp-≈ i≈j .fst

        e₁ : D .fobj (sOf j) .idx ._≈_ (D .fmor ⟪ e₀ ⟫ .idxf .func (dOf i)) (dOf j)
        e₁ = p .func-resp-≈ i≈j .snd

        legresp : D .fobj s .idx ._≈_ (D .fmor ⟪ pf ⟫ .idxf .func (dOf i)) (D .fmor ⟪ pf' ⟫ .idxf .func (dOf j))
        legresp = leg s .idxf .func-resp-≈ {i , pf} {j , pf'} i≈j

        -- ⟪_⟫ proofs are definitionally interchangeable, so fmor-comp relates
        -- the transport at pf to the two-step transport through e₀ and pf'.
        q₂ : D .fobj s .idx ._≈_ (D .fmor ⟪ pf' ⟫ .idxf .func (D .fmor ⟪ e₀ ⟫ .idxf .func (dOf i))) (D .fmor ⟪ pf ⟫ .idxf .func (dOf i))
        q₂ = D .fobj s .idx .sym (D .fmor-comp ⟪ pf' ⟫ ⟪ e₀ ⟫ .idxf-eq .func-eq (D .fobj (sOf i) .idx .refl))

        Dcomp : Category._≈_ cat (D .fmor ⟪ pf' ⟫ ∘cat D .fmor ⟪ e₀ ⟫) (D .fmor ⟪ pf ⟫)
        Dcomp = ≃-symC (D .fmor-comp ⟪ pf' ⟫ ⟪ e₀ ⟫)

        core : (D .fmor ⟪ pf' ⟫ .famf .transf (dOf j) ∘C (∐ S D) .fam .indexed-family.Fam.subst (p .func-resp-≈ i≈j))
               ≈C (D .fobj s .fam .indexed-family.Fam.subst legresp ∘C D .fmor ⟪ pf ⟫ .famf .transf (dOf i))
        core =
          ≈-transC (≈-symC (assocC _ _ _))
            (≈-transC (∘-cong₁C (D .fmor ⟪ pf' ⟫ .famf .natural e₁))
              (≈-transC (assocC _ _ _)
                (≈-transC (∘-cong₂C (≈-symC id-leftC))
                  (≈-transC (∘-cong₁C (D .fobj s .fam .indexed-family.Fam.trans* legresp q₂))
                    (≈-transC (assocC _ _ _)
                      (∘-cong₂C (Dcomp .famf-eq .transf-eq {dOf i})))))))

    -- y is the coproduct of its summands.
    fwd-h : Mor (∐ S E) y
    fwd-h .idxf .func (s , i , _) = i
    fwd-h .idxf .func-resp-≈ {s₁ , i , _} {s₂ , j , _} (_ , i≈j) = i≈j
    fwd-h .famf .transf (s , i , _) = idC (y .fam .indexed-family.Fam.fm i)
    fwd-h .famf .natural e = id-leftC

    bwd-h : Mor y (∐ S E)
    bwd-h .idxf .func i = sOf i , i , S .refl
    bwd-h .idxf .func-resp-≈ {i} {j} i≈j = p .func-resp-≈ i≈j .fst , i≈j
    bwd-h .famf .transf i = idC (y .fam .indexed-family.Fam.fm i)
    bwd-h .famf .natural e = ≈-transC id-leftC (≈-symC (≈-transC id-rightC id-rightC))

    h : Iso (∐ S E) y
    h .fwd = fwd-h
    h .bwd = bwd-h
    h .fwd∘bwd≈id .idxf-eq .func-eq i≈j = i≈j
    h .fwd∘bwd≈id .famf-eq .transf-eq = ≈-transC (∘-congC (y .fam .indexed-family.Fam.refl*) (≈-transC (∘-cong₂C id-leftC) id-leftC)) id-leftC
    h .bwd∘fwd≈id .idxf-eq .func-eq {s , i , pf} {s' , j , pf'} (w , i≈j) = S .trans pf w , i≈j
    h .bwd∘fwd≈id .famf-eq .transf-eq = ≈-transC (∘-congC (≈-transC id-rightC (y .fam .indexed-family.Fam.refl*)) (≈-transC id-leftC id-leftC)) id-leftC

    eq : ∀ s → Mor-∘ (f .fwd) (Mor-∘ (inj D s) (leg s)) ≃ Mor-∘ g (Mor-∘ (h .fwd) (inj E s))
    eq s .idxf-eq .func-eq {i , pf} {i' , pf'} i≈i' =
      x .idx .trans (f .fwd .idxf .func-resp-≈ apex-eq)
        (x .idx .trans (f .fwd∘bwd≈id .idxf-eq .func-eq (x .idx .refl))
                       (g .idxf .func-resp-≈ i≈i'))
      where
        apex-eq : (∐ S D) .idx ._≈_ (s , D .fmor ⟪ pf ⟫ .idxf .func (dOf i)) (p .func i)
        apex-eq = S .sym pf ,
          D .fobj (sOf i) .idx .trans
            (D .fobj (sOf i) .idx .sym (D .fmor-comp ⟪ S .sym pf ⟫ ⟪ pf ⟫ .idxf-eq .func-eq (D .fobj (sOf i) .idx .refl)))
            (D .fobj (sOf i) .idx .trans
              (D .fmor-cong {f₁ = ⟪ S .trans pf (S .sym pf) ⟫} {f₂ = ⟪ S .refl ⟫} tt .idxf-eq .func-eq (D .fobj (sOf i) .idx .refl))
              (D .fmor-id .idxf-eq .func-eq (D .fobj (sOf i) .idx .refl)))
    eq s .famf-eq .transf-eq {i , pf} =
      ≈-transC (∘-cong₂C (≈-transC id-leftC (∘-cong₂C (≈-transC id-leftC (≈-transC id-leftC (∘-cong₂C id-leftC))))))
        (≈-transC (∘-cong₂C (∘-cong₂C (≈-symC (assocC _ _ _))))
          (≈-transC (∘-cong₂C (≈-symC (assocC _ _ _)))
            (≈-transC (≈-symC (assocC _ _ _))
              (≈-transC (∘-cong₁C roundtrip)
                (≈-transC id-leftC
                  (≈-symC (≈-transC id-leftC (≈-transC (∘-cong₂C (≈-transC id-leftC id-leftC)) id-rightC))))))))
      where
        w : x .idx .Carrier
        w = g .idxf .func i

        ŝ : (∐ S D) .idx .Carrier
        ŝ = s , D .fmor ⟪ pf ⟫ .idxf .func (dOf i)

        symapex : (∐ S D) .idx ._≈_ (p .func i) ŝ
        symapex = pf , D .fobj s .idx .refl

        q₃ : x .idx ._≈_ (f .fwd .idxf .func (p .func i)) (f .fwd .idxf .func ŝ)
        q₃ = f .fwd .idxf .func-resp-≈ symapex

        EQ : x .idx ._≈_ (f .fwd .idxf .func ŝ) w
        EQ = x .idx .trans (x .idx .sym q₃) (f .fwd∘bwd≈id .idxf-eq .func-eq (x .idx .refl {w}))

        -- The leg's transport is the coproduct's subst along symapex, up to a
        -- vanishing refl-subst.
        insert : D .fmor ⟪ pf ⟫ .famf .transf (dOf i) ≈C (∐ S D) .fam .indexed-family.Fam.subst symapex
        insert = ≈-symC (≈-transC (∘-cong₁C (D .fobj s .fam .indexed-family.Fam.refl*)) id-leftC)

        -- Sending the summand back through the decomposition and out along the
        -- iso is the identity, by naturality and the iso's roundtrip.
        roundtrip : (x .fam .indexed-family.Fam.subst EQ
                      ∘C (f .fwd .famf .transf ŝ
                        ∘C (D .fmor ⟪ pf ⟫ .famf .transf (dOf i) ∘C f .bwd .famf .transf w)))
                    ≈C idC (x .fam .indexed-family.Fam.fm w)
        roundtrip =
          ≈-transC (∘-cong₂C (∘-cong₂C (∘-cong₁C insert)))
            (≈-transC (∘-cong₂C (≈-symC (assocC _ _ _)))
              (≈-transC (∘-cong₂C (∘-cong₁C (f .fwd .famf .natural symapex)))
                (≈-transC (∘-cong₂C (assocC _ _ _))
                  (≈-transC (≈-symC (assocC _ _ _))
                    (≈-transC (∘-cong₁C (≈-symC (x .fam .indexed-family.Fam.trans* EQ q₃)))
                      (≈-transC (∘-cong₂C (≈-symC id-leftC))
                        (f .fwd∘bwd≈id .famf-eq .transf-eq {w})))))))
