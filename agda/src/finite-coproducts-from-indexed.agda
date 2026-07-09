{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (lift)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import prop using (⟪_⟫; ∃ₛ)
open import categories using (Category; setoid→category; HasCoproducts)
open import prop-setoid using (Setoid; 𝟙; +-setoid; module ≈-Reasoning)
open import functor using (Functor; HasColimits; Colimit; IsColimit; NatTrans; NatIso; ≃-NatTrans; constF; colambda-unique; _∘F_)
open import finite-coproduct-functor using (preserve-chosen-coproducts)
open import indexed-family using (Fam; fam→functor)
import stable-coproducts
import stable-coproducts-indexed

module finite-coproducts-from-indexed where

-- Finite coproducts as the two-element instance of set-indexed coproducts: the
-- object and its universal property, its stability, and its functoriality.
module derive
  {o m e os es} {𝒞 : Category o m e}
  (LC : ∀ (S : Setoid os es) → HasColimits (setoid→category S) 𝒞)
  where

  private module 𝒞 = Category 𝒞
  open stable-coproducts-indexed LC
  open 𝒞.Iso
  open Colimit
  open NatTrans
  open Functor

  -- The two-element index and the two-object diagram, exposed so that a functor
  -- preserving set-indexed coproducts can be shown to preserve the derived ones.
  Two : Setoid os es
  Two = +-setoid 𝟙 𝟙

  pairFam : 𝒞.obj → 𝒞.obj → Fam Two 𝒞
  pairFam x y .Fam.fm (inj₁ _) = x
  pairFam x y .Fam.fm (inj₂ _) = y
  pairFam x y .Fam.subst {inj₁ _} {inj₁ _} _ = 𝒞.id _
  pairFam x y .Fam.subst {inj₂ _} {inj₂ _} _ = 𝒞.id _
  pairFam x y .Fam.refl* {inj₁ _} = 𝒞.≈-refl
  pairFam x y .Fam.refl* {inj₂ _} = 𝒞.≈-refl
  pairFam x y .Fam.trans* {inj₁ _} {inj₁ _} {inj₁ _} _ _ = 𝒞.≈-sym 𝒞.id-left
  pairFam x y .Fam.trans* {inj₂ _} {inj₂ _} {inj₂ _} _ _ = 𝒞.≈-sym 𝒞.id-left

  Dpair : 𝒞.obj → 𝒞.obj → Functor (setoid→category Two) 𝒞
  Dpair x y = fam→functor (pairFam x y)

  private
    copairCocone : ∀ {x y z} (f : x 𝒞.⇒ z) (g : y 𝒞.⇒ z) →
                   NatTrans (Dpair x y) (constF (setoid→category Two) z)
    copairCocone f g .transf (inj₁ _) = f
    copairCocone f g .transf (inj₂ _) = g
    copairCocone f g .natural {inj₁ _} {inj₁ _} _ = 𝒞.≈-trans 𝒞.id-left (𝒞.≈-sym 𝒞.id-right)
    copairCocone f g .natural {inj₂ _} {inj₂ _} _ = 𝒞.≈-trans 𝒞.id-left (𝒞.≈-sym 𝒞.id-right)

    ⊕ : 𝒞.obj → 𝒞.obj → 𝒞.obj
    ⊕ x y = ∐ Two (Dpair x y)

    ι₁ : ∀ {x y} → x 𝒞.⇒ ⊕ x y
    ι₁ {x} {y} = inj (Dpair x y) (inj₁ (lift tt))

    ι₂ : ∀ {x y} → y 𝒞.⇒ ⊕ x y
    ι₂ {x} {y} = inj (Dpair x y) (inj₂ (lift tt))

    ⟨_∣_⟩ : ∀ {x y z} → x 𝒞.⇒ z → y 𝒞.⇒ z → ⊕ x y 𝒞.⇒ z
    ⟨_∣_⟩ {x} {y} {z} f g = LC Two (Dpair x y) .colambda z (copairCocone f g)

    pin₁ : ∀ {x y z} (f : x 𝒞.⇒ z) (g : y 𝒞.⇒ z) → (⟨ f ∣ g ⟩ 𝒞.∘ ι₁) 𝒞.≈ f
    pin₁ {x} {y} {z} f g =
      LC Two (Dpair x y) .colambda-coeval z (copairCocone f g) .≃-NatTrans.transf-eq (inj₁ (lift tt))

    pin₂ : ∀ {x y z} (f : x 𝒞.⇒ z) (g : y 𝒞.⇒ z) → (⟨ f ∣ g ⟩ 𝒞.∘ ι₂) 𝒞.≈ g
    pin₂ {x} {y} {z} f g =
      LC Two (Dpair x y) .colambda-coeval z (copairCocone f g) .≃-NatTrans.transf-eq (inj₂ (lift tt))

    pext : ∀ {x y z} (f : ⊕ x y 𝒞.⇒ z) → ⟨ f 𝒞.∘ ι₁ ∣ f 𝒞.∘ ι₂ ⟩ 𝒞.≈ f
    pext {x} {y} {z} f = colambda-unique (LC Two (Dpair x y) .isColimit) uni
      where
        uni : ∀ s → (⟨ f 𝒞.∘ ι₁ ∣ f 𝒞.∘ ι₂ ⟩ 𝒞.∘ inj (Dpair x y) s) 𝒞.≈ (f 𝒞.∘ inj (Dpair x y) s)
        uni (inj₁ _) = pin₁ (f 𝒞.∘ ι₁) (f 𝒞.∘ ι₂)
        uni (inj₂ _) = pin₂ (f 𝒞.∘ ι₁) (f 𝒞.∘ ι₂)

    pcong : ∀ {x y z} {f₁ f₂ : x 𝒞.⇒ z} {g₁ g₂ : y 𝒞.⇒ z} →
            f₁ 𝒞.≈ f₂ → g₁ 𝒞.≈ g₂ → ⟨ f₁ ∣ g₁ ⟩ 𝒞.≈ ⟨ f₂ ∣ g₂ ⟩
    pcong {x} {y} {z} f₁≈f₂ g₁≈g₂ = LC Two (Dpair x y) .colambda-cong coconeEq
      where
        coconeEq : ≃-NatTrans (copairCocone _ _) (copairCocone _ _)
        coconeEq .≃-NatTrans.transf-eq (inj₁ _) = f₁≈f₂
        coconeEq .≃-NatTrans.transf-eq (inj₂ _) = g₁≈g₂

  -- Finite coproducts derived from the two-element set-indexed coproduct.
  coproducts-from-indexed : HasCoproducts 𝒞
  coproducts-from-indexed .HasCoproducts.coprod = ⊕
  coproducts-from-indexed .HasCoproducts.in₁ = ι₁
  coproducts-from-indexed .HasCoproducts.in₂ = ι₂
  coproducts-from-indexed .HasCoproducts.copair = ⟨_∣_⟩
  coproducts-from-indexed .HasCoproducts.copair-cong = pcong
  coproducts-from-indexed .HasCoproducts.copair-in₁ = pin₁
  coproducts-from-indexed .HasCoproducts.copair-in₂ = pin₂
  coproducts-from-indexed .HasCoproducts.copair-ext = pext

  ------------------------------------------------------------------------------
  -- Functoriality of set-indexed coproducts: a map of diagrams induces a map of
  -- coproducts, and a natural isomorphism an isomorphism.

  map-cocone : ∀ {S} {D₁ D₂ : Functor (setoid→category S) 𝒞} (α : NatTrans D₁ D₂) →
               NatTrans D₁ (constF (setoid→category S) (∐ S D₂))
  map-cocone {S} {D₁} {D₂} α .transf s = inj D₂ s 𝒞.∘ α .transf s
  map-cocone {S} {D₁} {D₂} α .natural {s} {s'} ⟪ e ⟫ = begin
      𝒞.id _ 𝒞.∘ (inj D₂ s 𝒞.∘ α .transf s)
    ≈⟨ 𝒞.id-left ⟩
      inj D₂ s 𝒞.∘ α .transf s
    ≈⟨ 𝒞.∘-cong (𝒞.≈-trans (𝒞.≈-sym 𝒞.id-left) (LC S D₂ .cocone .natural ⟪ e ⟫)) 𝒞.≈-refl ⟩
      (inj D₂ s' 𝒞.∘ D₂ .fmor ⟪ e ⟫) 𝒞.∘ α .transf s
    ≈⟨ 𝒞.assoc _ _ _ ⟩
      inj D₂ s' 𝒞.∘ (D₂ .fmor ⟪ e ⟫ 𝒞.∘ α .transf s)
    ≈⟨ 𝒞.∘-cong 𝒞.≈-refl (α .natural ⟪ e ⟫) ⟩
      inj D₂ s' 𝒞.∘ (α .transf s' 𝒞.∘ D₁ .fmor ⟪ e ⟫)
    ≈⟨ 𝒞.≈-sym (𝒞.assoc _ _ _) ⟩
      (inj D₂ s' 𝒞.∘ α .transf s') 𝒞.∘ D₁ .fmor ⟪ e ⟫
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

  ∐-map : ∀ {S} {D₁ D₂ : Functor (setoid→category S) 𝒞} → NatTrans D₁ D₂ → ∐ S D₁ 𝒞.⇒ ∐ S D₂
  ∐-map {S} {D₁} {D₂} α = LC S D₁ .colambda (∐ S D₂) (map-cocone α)

  ∐-map-coeval : ∀ {S} {D₁ D₂ : Functor (setoid→category S) 𝒞} (α : NatTrans D₁ D₂) (s : S .Setoid.Carrier) →
                 (∐-map α 𝒞.∘ inj D₁ s) 𝒞.≈ (inj D₂ s 𝒞.∘ α .transf s)
  ∐-map-coeval {S} {D₁} {D₂} α s = LC S D₁ .colambda-coeval (∐ S D₂) (map-cocone α) .≃-NatTrans.transf-eq s

  ∐-iso : ∀ {S} {D₁ D₂ : Functor (setoid→category S) 𝒞} → NatIso D₁ D₂ → 𝒞.Iso (∐ S D₁) (∐ S D₂)
  ∐-iso {S} {D₁} {D₂} α .fwd = ∐-map (α .NatIso.transform)
  ∐-iso {S} {D₁} {D₂} α .bwd = ∐-map (NatIso.transform⁻¹ α)
  ∐-iso {S} {D₁} {D₂} α .fwd∘bwd≈id = colambda-unique (LC S D₂ .isColimit) uni
    where
      T  = α .NatIso.transform
      T⁻ = NatIso.transform⁻¹ α
      uni : ∀ s → ((∐-map T 𝒞.∘ ∐-map T⁻) 𝒞.∘ inj D₂ s) 𝒞.≈ (𝒞.id _ 𝒞.∘ inj D₂ s)
      uni s = begin
          (∐-map T 𝒞.∘ ∐-map T⁻) 𝒞.∘ inj D₂ s
        ≈⟨ 𝒞.assoc _ _ _ ⟩
          ∐-map T 𝒞.∘ (∐-map T⁻ 𝒞.∘ inj D₂ s)
        ≈⟨ 𝒞.∘-cong 𝒞.≈-refl (∐-map-coeval T⁻ s) ⟩
          ∐-map T 𝒞.∘ (inj D₁ s 𝒞.∘ T⁻ .transf s)
        ≈⟨ 𝒞.≈-sym (𝒞.assoc _ _ _) ⟩
          (∐-map T 𝒞.∘ inj D₁ s) 𝒞.∘ T⁻ .transf s
        ≈⟨ 𝒞.∘-cong (∐-map-coeval T s) 𝒞.≈-refl ⟩
          (inj D₂ s 𝒞.∘ T .transf s) 𝒞.∘ T⁻ .transf s
        ≈⟨ 𝒞.assoc _ _ _ ⟩
          inj D₂ s 𝒞.∘ (T .transf s 𝒞.∘ T⁻ .transf s)
        ≈⟨ 𝒞.∘-cong 𝒞.≈-refl (α .NatIso.transf-iso s .Category.IsIso.f∘inverse≈id) ⟩
          inj D₂ s 𝒞.∘ 𝒞.id _
        ≈⟨ 𝒞.≈-trans 𝒞.id-right (𝒞.≈-sym 𝒞.id-left) ⟩
          𝒞.id _ 𝒞.∘ inj D₂ s
        ∎
        where open ≈-Reasoning 𝒞.isEquiv
  ∐-iso {S} {D₁} {D₂} α .bwd∘fwd≈id = colambda-unique (LC S D₁ .isColimit) uni
    where
      T  = α .NatIso.transform
      T⁻ = NatIso.transform⁻¹ α
      uni : ∀ s → ((∐-map T⁻ 𝒞.∘ ∐-map T) 𝒞.∘ inj D₁ s) 𝒞.≈ (𝒞.id _ 𝒞.∘ inj D₁ s)
      uni s = begin
          (∐-map T⁻ 𝒞.∘ ∐-map T) 𝒞.∘ inj D₁ s
        ≈⟨ 𝒞.assoc _ _ _ ⟩
          ∐-map T⁻ 𝒞.∘ (∐-map T 𝒞.∘ inj D₁ s)
        ≈⟨ 𝒞.∘-cong 𝒞.≈-refl (∐-map-coeval T s) ⟩
          ∐-map T⁻ 𝒞.∘ (inj D₂ s 𝒞.∘ T .transf s)
        ≈⟨ 𝒞.≈-sym (𝒞.assoc _ _ _) ⟩
          (∐-map T⁻ 𝒞.∘ inj D₂ s) 𝒞.∘ T .transf s
        ≈⟨ 𝒞.∘-cong (∐-map-coeval T⁻ s) 𝒞.≈-refl ⟩
          (inj D₁ s 𝒞.∘ T⁻ .transf s) 𝒞.∘ T .transf s
        ≈⟨ 𝒞.assoc _ _ _ ⟩
          inj D₁ s 𝒞.∘ (T⁻ .transf s 𝒞.∘ T .transf s)
        ≈⟨ 𝒞.∘-cong 𝒞.≈-refl (α .NatIso.transf-iso s .Category.IsIso.inverse∘f≈id) ⟩
          inj D₁ s 𝒞.∘ 𝒞.id _
        ≈⟨ 𝒞.≈-trans 𝒞.id-right (𝒞.≈-sym 𝒞.id-left) ⟩
          𝒞.id _ 𝒞.∘ inj D₁ s
        ∎
        where open ≈-Reasoning 𝒞.isEquiv

  ------------------------------------------------------------------------------
  -- Set-indexed stability yields binary stability for the derived coproducts.

  private
    module SC = stable-coproducts coproducts-from-indexed

  stable-from-indexed : IdxStable → SC.Stable
  stable-from-indexed idxstable {x₁} {x₂} {x} {y} f g = sb
    where
      module IB = IdxStableBits (idxstable {Two} {Dpair x₁ x₂} f g)

      yy₁ = IB.E .fobj (inj₁ (lift tt))
      yy₂ = IB.E .fobj (inj₂ (lift tt))

      -- E and the two-element diagram on its objects agree up to identity.
      natiso : NatIso (Dpair yy₁ yy₂) IB.E
      natiso .NatIso.transform .transf (inj₁ _) = 𝒞.id _
      natiso .NatIso.transform .transf (inj₂ _) = 𝒞.id _
      natiso .NatIso.transform .natural {inj₁ _} {inj₁ _} _ =
        𝒞.≈-trans 𝒞.id-right (𝒞.≈-trans (IB.E .fmor-id) (𝒞.≈-sym 𝒞.id-left))
      natiso .NatIso.transform .natural {inj₂ _} {inj₂ _} _ =
        𝒞.≈-trans 𝒞.id-right (𝒞.≈-trans (IB.E .fmor-id) (𝒞.≈-sym 𝒞.id-left))
      natiso .NatIso.transf-iso (inj₁ _) .Category.IsIso.inverse = 𝒞.id _
      natiso .NatIso.transf-iso (inj₂ _) .Category.IsIso.inverse = 𝒞.id _
      natiso .NatIso.transf-iso (inj₁ _) .Category.IsIso.f∘inverse≈id = 𝒞.id-left
      natiso .NatIso.transf-iso (inj₂ _) .Category.IsIso.f∘inverse≈id = 𝒞.id-left
      natiso .NatIso.transf-iso (inj₁ _) .Category.IsIso.inverse∘f≈id = 𝒞.id-left
      natiso .NatIso.transf-iso (inj₂ _) .Category.IsIso.inverse∘f≈id = 𝒞.id-left

      -- The comparison iso commutes with the injections, so the factorisation
      -- equations transport from IB.E's coproduct to the derived one.
      adj₁ = 𝒞.≈-sym (𝒞.≈-trans (𝒞.assoc _ _ _)
               (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-trans (∐-map-coeval (natiso .NatIso.transform) (inj₁ (lift tt))) 𝒞.id-right)))
      adj₂ = 𝒞.≈-sym (𝒞.≈-trans (𝒞.assoc _ _ _)
               (𝒞.∘-cong 𝒞.≈-refl (𝒞.≈-trans (∐-map-coeval (natiso .NatIso.transform) (inj₂ (lift tt))) 𝒞.id-right)))

      sb : SC.StableBits f g
      sb .SC.StableBits.y₁  = yy₁
      sb .SC.StableBits.y₂  = yy₂
      sb .SC.StableBits.h₁  = IB.leg (inj₁ (lift tt))
      sb .SC.StableBits.h₂  = IB.leg (inj₂ (lift tt))
      sb .SC.StableBits.h   = 𝒞.Iso-trans (∐-iso natiso) IB.h
      sb .SC.StableBits.eq₁ = 𝒞.≈-trans (IB.eq (inj₁ (lift tt))) (𝒞.∘-cong 𝒞.≈-refl adj₁)
      sb .SC.StableBits.eq₂ = 𝒞.≈-trans (IB.eq (inj₂ (lift tt))) (𝒞.∘-cong 𝒞.≈-refl adj₂)

-- A functor preserving set-indexed coproducts preserves the finite coproducts
-- derived from them (the two-element instance).
module preserve
  {oA mA eA oB mB eB}
  {𝒜 : Category oA mA eA} {ℬ : Category oB mB eB}
  where

  private
    module 𝒜 = Category 𝒜
    module ℬ = Category ℬ

  open Functor
  open NatTrans

  module _
    {os es}
    (𝒜CL : ∀ (S : Setoid os es) → HasColimits (setoid→category S) 𝒜)
    (ℬCL : ∀ (S : Setoid os es) → HasColimits (setoid→category S) ℬ)
    (F : Functor 𝒜 ℬ)
    (F-DC : ∀ (S : Setoid os es) (D : Functor (setoid→category S) 𝒜) →
            ∃ₛ (ℬ.Iso (Colimit.apex (ℬCL S (F ∘F D))) (F .fobj (Colimit.apex (𝒜CL S D))))
               (λ i → ∀ s → (ℬ.Iso.fwd i ℬ.∘ Colimit.cocone (ℬCL S (F ∘F D)) .transf s) ℬ.≈
                            F .fmor (Colimit.cocone (𝒜CL S D) .transf s)))
    where

    private
      module SA = derive 𝒜CL
      module SB = derive ℬCL
      module 𝒜CP = HasCoproducts SA.coproducts-from-indexed
      module ℬCP = HasCoproducts SB.coproducts-from-indexed

    open ℬ.Iso
    open ℬ.IsIso

    preserve-from-indexed : preserve-chosen-coproducts F SA.coproducts-from-indexed SB.coproducts-from-indexed
    preserve-from-indexed {x} {y} =
      ℬ.IsIso-cong
        (ℬ.≈-trans (ℬ.≈-sym (ℬCP.copair-ext (theIso .fwd))) (ℬCP.copair-cong onIn₁ onIn₂))
        fwd-iso
      where
        module FI = ∃ₛ (F-DC SA.Two (SA.Dpair x y))

        -- SB.Dpair (F x) (F y) and F ∘F SA.Dpair x y agree up to identity.
        ψ : NatIso (SB.Dpair (F .fobj x) (F .fobj y)) (F ∘F SA.Dpair x y)
        ψ .NatIso.transform .transf (inj₁ _) = ℬ.id _
        ψ .NatIso.transform .transf (inj₂ _) = ℬ.id _
        ψ .NatIso.transform .natural {inj₁ _} {inj₁ _} _ =
          ℬ.≈-trans ℬ.id-right (ℬ.≈-trans (F .fmor-id) (ℬ.≈-sym ℬ.id-left))
        ψ .NatIso.transform .natural {inj₂ _} {inj₂ _} _ =
          ℬ.≈-trans ℬ.id-right (ℬ.≈-trans (F .fmor-id) (ℬ.≈-sym ℬ.id-left))
        ψ .NatIso.transf-iso (inj₁ _) .inverse = ℬ.id _
        ψ .NatIso.transf-iso (inj₂ _) .inverse = ℬ.id _
        ψ .NatIso.transf-iso (inj₁ _) .f∘inverse≈id = ℬ.id-left
        ψ .NatIso.transf-iso (inj₂ _) .f∘inverse≈id = ℬ.id-left
        ψ .NatIso.transf-iso (inj₁ _) .inverse∘f≈id = ℬ.id-left
        ψ .NatIso.transf-iso (inj₂ _) .inverse∘f≈id = ℬ.id-left

        theIso : ℬ.Iso (ℬCP.coprod (F .fobj x) (F .fobj y)) (F .fobj (𝒜CP.coprod x y))
        theIso = ℬ.Iso-trans (SB.∐-iso ψ) FI.fst

        fwd-iso : ℬ.IsIso (theIso .fwd)
        fwd-iso .inverse = theIso .bwd
        fwd-iso .f∘inverse≈id = theIso .fwd∘bwd≈id
        fwd-iso .inverse∘f≈id = theIso .bwd∘fwd≈id

        -- theIso.fwd sends each injection to F of the corresponding one.
        onIn₁ = ℬ.≈-trans (ℬ.assoc _ _ _)
                  (ℬ.≈-trans (ℬ.∘-cong ℬ.≈-refl
                               (ℬ.≈-trans (SB.∐-map-coeval (ψ .NatIso.transform) (inj₁ (lift tt))) ℬ.id-right))
                             (FI.snd (inj₁ (lift tt))))
        onIn₂ = ℬ.≈-trans (ℬ.assoc _ _ _)
                  (ℬ.≈-trans (ℬ.∘-cong ℬ.≈-refl
                               (ℬ.≈-trans (SB.∐-map-coeval (ψ .NatIso.transform) (inj₂ (lift tt))) ℬ.id-right))
                             (FI.snd (inj₂ (lift tt))))

