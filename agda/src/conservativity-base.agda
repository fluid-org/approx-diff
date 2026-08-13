{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The shared base of the Grothendieck logical relations: Kripke predicates over 𝒞, the nerve of
-- F, the coverage given by coproduct decompositions of a stage, and the closure operator and
-- predicate system it generates. This is everything the construction needs before the glued
-- category itself, and it depends on neither the exponentials nor the monads, so a development
-- that builds its own glued category can instantiate this alone.
------------------------------------------------------------------------------

open import Level using (Level; Lift; lift; lower; _⊔_; 0ℓ) renaming (suc to lsuc)
open import prop using (LiftP; lift)
open import basics using (IsClosureOp; IsJoin; IsMeet; IsBigJoin; IsPreorder)
open import categories using (Category; HasProducts; HasCoproducts; setoid→category)
open import functor
open import prop-setoid using (module ≈-Reasoning; IsEquivalence; Setoid)
open import predicate-system using (PredicateSystem)
open import stable-coproducts using (StableBits)
import stable-coproducts-indexed
import finite-coproducts-from-indexed
import setoid-predicate
import closure-predicate

module conservativity-base
  {o₁ o₂ m e}
  (𝒞 : Category o₁ m e)
  (𝒞DC : ∀ (S : Setoid 0ℓ 0ℓ) → HasColimits (setoid→category S) 𝒞)
  (𝒞istable : stable-coproducts-indexed.IdxStable 𝒞DC)
  (𝒟 : Category o₂ m e)
  (F  : Functor 𝒞 𝒟)
  where

open Functor
open NatTrans
open ≃-NatTrans

-- The finite coproducts and their stability are the two-element instance of the set-indexed
-- structure.
private
  module 𝒞d = finite-coproducts-from-indexed.derive 𝒞DC

𝒞CP = 𝒞d.coproducts-from-indexed
stable = 𝒞d.stable-from-indexed 𝒞istable

private
  module 𝒞 = Category 𝒞
  module 𝒞CP = HasCoproducts 𝒞CP
  module 𝒟 = Category 𝒟


------------------------------------------------------------------------------
-- Kripke Predicates “of varying arity”
open import yoneda (o₁ ⊔ o₂ ⊔ m ⊔ e ⊔ lsuc 0ℓ) 𝒞 renaming (PSh to PSh⟨𝒞⟩; products to PSh⟨𝒞⟩-products) using (module DayMonad; module UnaryDay; Coend; Cowedge) public
open import yoneda (o₁ ⊔ o₂ ⊔ m ⊔ e ⊔ lsuc 0ℓ) 𝒟 renaming (よ to 𝒟よ) using () public

private
  module PSh⟨𝒞⟩ = Category PSh⟨𝒞⟩

-- FIXME: define PSh(F) : PSh⟨𝒟⟩ ⇒ PSh⟨𝒞⟩, then G is composition of this and yoneda

G : Functor 𝒟 PSh⟨𝒞⟩
G .fobj x = 𝒟よ .fobj x ∘F opF F
G .fmor f = 𝒟よ .fmor f ∘H id _
G .fmor-cong f₁≈f₂ = ∘H-cong (𝒟よ .fmor-cong f₁≈f₂) (≃-isEquivalence .IsEquivalence.refl)
G .fmor-id = begin
    𝒟よ .fmor (𝒟.id _) ∘H id _
  ≈⟨ ∘H-cong (𝒟よ .fmor-id) (≃-isEquivalence .IsEquivalence.refl) ⟩
    id (𝒟よ .fobj _) ∘H id (opF F)
  ≈⟨ H-id ⟩
    PSh⟨𝒞⟩.id _
  ∎ where open ≈-Reasoning PSh⟨𝒞⟩.isEquiv
G .fmor-comp f g = begin
    𝒟よ .fmor (f 𝒟.∘ g) ∘H id _
  ≈⟨ ∘H-cong (𝒟よ .fmor-comp f g) (≃-isEquivalence .IsEquivalence.sym NT-id-left) ⟩
    (𝒟よ .fmor f ∘ 𝒟よ .fmor g) ∘H (id _ ∘ id _)
  ≈⟨ interchange _ _ _ _ ⟩
    (𝒟よ .fmor f ∘H id _) PSh⟨𝒞⟩.∘ (𝒟よ .fmor g ∘H id _)
  ∎ where open ≈-Reasoning PSh⟨𝒞⟩.isEquiv


------------------------------------------------------------------------------
-- Presheaf predicates
open import presheaf-predicate (o₁ ⊔ o₂ ⊔ m ⊔ e ⊔ lsuc 0ℓ) 𝒞
  renaming (system to PSh⟨𝒞⟩-system; Predicate to PShPredicate)
  using (_⊑_; module CoverMonad;
         _++_; _⟨_⟩; ⊑-isPreorder; _[_]; []-++; ++-isJoin; _&&_; &&-isMeet; TT; TT-isTop;
         ⋁; module Monad-hat-pred; &&-++-distrib; &&-⋁-distrib; &&-⟨⟩-frobenius; ⟨⟩-[]-BC)
  public

module PSh⟨𝒞⟩-system = PredicateSystem PSh⟨𝒞⟩-system

open PShPredicate
open setoid-predicate.Predicate
open setoid-predicate._⊑_
open _⊑_

------------------------------------------------------------------------------
-- The coverage generating the closure: coproduct decompositions of the stage,
-- binary or set-indexed.
module SI = stable-coproducts-indexed 𝒞DC

private
  Levℓ : Level
  Levℓ = o₁ ⊔ o₂ ⊔ m ⊔ e ⊔ lsuc 0ℓ

data Side : Set Levℓ where
  inl inr : Side

record BinCover (y : 𝒞.obj) : Set Levℓ where
  field
    y₁  : 𝒞.obj
    y₂  : 𝒞.obj
    iso : 𝒞.Iso (𝒞CP.coprod y₁ y₂) y

record IdxCover (y : 𝒞.obj) : Set Levℓ where
  field
    S   : Setoid 0ℓ 0ℓ
    D   : Functor (setoid→category S) 𝒞
    iso : 𝒞.Iso (SI.∐ S D) y

data Cover (y : 𝒞.obj) : Set Levℓ where
  bin : BinCover y → Cover y
  idx : IdxCover y → Cover y

CIx : ∀ {y} → Cover y → Set Levℓ
CIx (bin _) = Side
CIx (idx c) = Lift Levℓ (c .IdxCover.S .Setoid.Carrier)

cDom : ∀ {y} (c : Cover y) → CIx c → 𝒞.obj
cDom (bin c) inl = c .BinCover.y₁
cDom (bin c) inr = c .BinCover.y₂
cDom (idx c) (lift s) = c .IdxCover.D .fobj s

cInj : ∀ {y} (c : Cover y) (s : CIx c) → cDom c s 𝒞.⇒ y
cInj (bin c) inl = c .BinCover.iso .𝒞.Iso.fwd 𝒞.∘ 𝒞CP.in₁
cInj (bin c) inr = c .BinCover.iso .𝒞.Iso.fwd 𝒞.∘ 𝒞CP.in₂
cInj (idx c) (lift s) = c .IdxCover.iso .𝒞.Iso.fwd 𝒞.∘ SI.inj (c .IdxCover.D) s

module CvM = CoverMonad Cover CIx cDom cInj

-- Covers pull back along any morphism: binary by stability of the finite
-- coproducts, set-indexed by stability of the set-indexed ones.
covPull : ∀ {x y} (c : Cover x) (g : y 𝒞.⇒ x) → CvM.CoverPullback c g
covPull (bin c) g = pb
  where
    open CvM.CoverPullback
    stb = stable (c .BinCover.iso) g

    pb : CvM.CoverPullback (bin c) g
    pb .cover = bin (record { y₁ = stb .StableBits.y₁ ; y₂ = stb .StableBits.y₂ ; iso = stb .StableBits.h })
    pb .reix s = s
    pb .leg inl = stb .StableBits.h₁
    pb .leg inr = stb .StableBits.h₂
    pb .eq inl = 𝒞.≈-trans (𝒞.assoc _ _ _) (stb .StableBits.eq₁)
    pb .eq inr = 𝒞.≈-trans (𝒞.assoc _ _ _) (stb .StableBits.eq₂)
covPull (idx c) g = pb
  where
    open CvM.CoverPullback
    stb = 𝒞istable (c .IdxCover.iso) g

    pb : CvM.CoverPullback (idx c) g
    pb .cover = idx (record { S = c .IdxCover.S ; D = stb .SI.IdxStableBits.E ; iso = stb .SI.IdxStableBits.h })
    pb .reix (lift s) = lift s
    pb .leg (lift s) = stb .SI.IdxStableBits.leg s
    pb .eq (lift s) = 𝒞.≈-trans (𝒞.assoc _ _ _) (stb .SI.IdxStableBits.eq s)

open CvM public
open CvM.Closure covPull public

------------------------------------------------------------------------------
-- The closed predicates: those that absorb the cover closure.
module CP = closure-predicate PSh⟨𝒞⟩-system closureOp
open CP using (system; embed; module 𝐂Monad) public
