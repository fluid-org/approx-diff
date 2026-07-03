{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ; suc)
open import prop-setoid using (Setoid; IsEquivalence)
open import categories using (Category; HasTerminal; IsTerminal; HasInitial; IsInitial; HasProducts; HasCoproducts)
open import commutative-semiring using (CommutativeSemiring)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products; biproduct-iso; biproducts→coproducts)
open import commutative-monoid using (CommutativeMonoid)
open import functor using (Functor)
import finite-product-functor
import semimodule

-- Category SDSemiMod of self-dual semimodules and linear maps.
module sd-semimodule {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module SemiMod = semimodule S
open SemiMod using (_⇒_; _≈m_; id; _∘_)

module _ where
  private module S = SemiMod.S
  open SemiMod using (Semimodule; terminal)
  open SemiMod.Semimodule using (Carrier; _≈_; refl; sym; trans; +-cong; +-comm; +-lunit)
  open SemiMod._⇒_
  open SemiMod._≈m_
  open import prop-setoid using () renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
  open import prop using (tt; proj₁; proj₂; _⇔_; _,_)
  open import Data.Product using (_,_)
  ------------------------------------------------------------------------------
  -- Duality

  -- The linear measurements of M.
  Dual : Semimodule → Semimodule
  Dual M = M SemiMod.⊸ SemiMod.𝕀

  open Category SemiMod.cat using (≈-trans; ≈-sym; ≈-refl; ∘-cong; assoc; id-left; Iso; IsIso→Iso; Iso-trans; Iso-sym)

  -- Pairing ⟨ x , y ⟩ = (d x) y induced by a self-duality; a measure of the extent to which x and y overlap.
  pairing : ∀ {M} → Iso M (Dual M) → M .Carrier → M .Carrier → S.Carrier
  pairing M≅M* x y = M≅M* .Iso.fwd .*→* ._⇒s_.func x .*→* ._⇒s_.func y

  -- Isomorphisms M ≅ Dual M are equivalent to certain kinds of bilinear maps:
  --
  --   M ⇒ M SemiMod.⊸ SemiMod.𝕀
  -- ≅ M ⊗ M ⇒ SemiMod.𝕀
  --
  -- When the original map is an isomorphism, then can this property be
  -- stated in terms of the bilinear map?
  --
  -- Non-degeneracy: ∀ x → x ≠ ε → ∃ y → ⟨ x , y ⟩ ≠ ε

  -- forward map: M ⇒ M SemiMod.⊸ I
  --              x ↦ y ↦ ⟨ x , y ⟩
  --
  -- backward map: (M SemiMod.⊸ I) ⇒ M
  --               f ↦ Σ f(eᵢ) eᵢ
  -- In finite dimensions, equivalent to unimodularity?

  ------------------------------------------------------------------------------
  -- Transpose: the contravariant action of Dual, f ↦ (_ ∘ f).

  open CMonEnriched SemiMod.cmon-enriched using (homCM; _+m_; εm; comp-bilinear₁; comp-bilinear-ε₁; comp-bilinear-ε₂)

  infix 25 _ᵀ

  _ᵀ : ∀ {M N} → M ⇒ N → Dual N ⇒ Dual M
  (f ᵀ) .*→* ._⇒s_.func φ = φ ∘ f
  (f ᵀ) .*→* ._⇒s_.func-resp-≈ φ≈ψ .*≈* ._≈s_.func-eq x≈y =
    φ≈ψ .*≈* ._≈s_.func-eq (f .func-resp-≈ x≈y)
  (f ᵀ) .preserve-ze = comp-bilinear-ε₁ f
  (f ᵀ) .preserve-+ {φ} {ψ} = comp-bilinear₁ φ ψ f
  (f ᵀ) .preserve-· {s} {φ} .*≈* ._≈s_.func-eq x≈y =
    S.·-cong S.refl (φ .func-resp-≈ (f .func-resp-≈ x≈y))

  ᵀ-cong : ∀ {M N} {f g : M ⇒ N} → f ≈m g → f ᵀ ≈m g ᵀ
  ᵀ-cong f≈g .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈y =
    φ≈ψ .*≈* ._≈s_.func-eq (f≈g .*≈* ._≈s_.func-eq x≈y)

  ᵀ-id : ∀ {M} → (id M) ᵀ ≈m id (Dual M)
  ᵀ-id .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈y = φ≈ψ .*≈* ._≈s_.func-eq x≈y

  ᵀ-comp : ∀ {M N O} (g : N ⇒ O) (f : M ⇒ N) → (g ∘ f) ᵀ ≈m f ᵀ ∘ g ᵀ
  ᵀ-comp g f .*≈* ._≈s_.func-eq φ≈ψ .*≈* ._≈s_.func-eq x≈y =
    φ≈ψ .*≈* ._≈s_.func-eq (g .func-resp-≈ (f .func-resp-≈ x≈y))

  -- Additivity.
  ᵀ-+ : ∀ {M N} (f g : M ⇒ N) → (f +m g) ᵀ ≈m f ᵀ +m g ᵀ
  ᵀ-+ f g .*≈* ._≈s_.func-eq {φ} φ≈ψ .*≈* ._≈s_.func-eq x≈y =
    trans SemiMod.𝕀 (φ .preserve-+)
      (+-cong SemiMod.𝕀 (φ≈ψ .*≈* ._≈s_.func-eq (f .func-resp-≈ x≈y)) (φ≈ψ .*≈* ._≈s_.func-eq (g .func-resp-≈ x≈y)))

  ᵀ-ε : ∀ {M N} → (εm {M} {N}) ᵀ ≈m εm
  ᵀ-ε .*≈* ._≈s_.func-eq {φ} _ = comp-bilinear-ε₂ φ

  module _ {M N} where
    open Biproduct (SemiMod.biproduct M N) using (in₁; in₂; id-1; id-2; zero-1; zero-2; id-+)

    Dual-preserves-⊕ : Biproduct SemiMod.cmon-enriched (Dual M) (Dual N)
    Dual-preserves-⊕ .Biproduct.prod = Dual (M SemiMod.⊕ N)
    Dual-preserves-⊕ .Biproduct.p₁ = in₁ ᵀ
    Dual-preserves-⊕ .Biproduct.p₂ = in₂ ᵀ
    Dual-preserves-⊕ .Biproduct.in₁ = SemiMod.p₁ ᵀ
    Dual-preserves-⊕ .Biproduct.in₂ = SemiMod.p₂ ᵀ
    Dual-preserves-⊕ .Biproduct.id-1 = ≈-trans (≈-sym (ᵀ-comp SemiMod.p₁ in₁)) (≈-trans (ᵀ-cong id-1) ᵀ-id)
    Dual-preserves-⊕ .Biproduct.id-2 = ≈-trans (≈-sym (ᵀ-comp SemiMod.p₂ in₂)) (≈-trans (ᵀ-cong id-2) ᵀ-id)
    Dual-preserves-⊕ .Biproduct.zero-1 = ≈-trans (≈-sym (ᵀ-comp SemiMod.p₂ in₁)) (≈-trans (ᵀ-cong zero-2) ᵀ-ε)
    Dual-preserves-⊕ .Biproduct.zero-2 = ≈-trans (≈-sym (ᵀ-comp SemiMod.p₁ in₂)) (≈-trans (ᵀ-cong zero-1) ᵀ-ε)
    Dual-preserves-⊕ .Biproduct.id-+ =
      ≈-trans (homCM _ _ .CommutativeMonoid.+-cong (≈-sym (ᵀ-comp in₁ SemiMod.p₁)) (≈-sym (ᵀ-comp in₂ SemiMod.p₂)))
        (≈-trans (≈-sym (ᵀ-+ (in₁ ∘ SemiMod.p₁) (in₂ ∘ SemiMod.p₂))) (≈-trans (ᵀ-cong id-+) ᵀ-id))

  ------------------------------------------------------------------------------
  -- Base case SemiMod.𝕀 ≅ Dual SemiMod.𝕀 for self-duality.

  𝕀≅𝕀* : Iso SemiMod.𝕀 (Dual SemiMod.𝕀)
  𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func x = a S.· x
  𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func-resp-≈ x≈y = S.·-cong S.refl x≈y
  𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-ze = S.ε-annihilᵣ
  𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-+ = S.·-+-distribₗ
  𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func a .preserve-· =
    S.trans (S.sym S.·-assoc) (S.trans (S.·-cong S.·-comm S.refl) S.·-assoc)
  𝕀≅𝕀* .Iso.fwd .*→* ._⇒s_.func-resp-≈ a≈b .*≈* ._≈s_.func-eq x≈y = S.·-cong a≈b x≈y
  𝕀≅𝕀* .Iso.fwd .preserve-ze .*≈* ._≈s_.func-eq _ = S.ε-annihilₗ
  𝕀≅𝕀* .Iso.fwd .preserve-+ .*≈* ._≈s_.func-eq x≈y =
    S.trans S.·-+-distribᵣ (S.+-cong (S.·-cong S.refl x≈y) (S.·-cong S.refl x≈y))
  𝕀≅𝕀* .Iso.fwd .preserve-· .*≈* ._≈s_.func-eq x≈y =
    S.trans S.·-assoc (S.·-cong S.refl (S.·-cong S.refl x≈y))
  𝕀≅𝕀* .Iso.bwd .*→* ._⇒s_.func φ = φ .func S.ι
  𝕀≅𝕀* .Iso.bwd .*→* ._⇒s_.func-resp-≈ φ≈ψ = φ≈ψ .*≈* ._≈s_.func-eq S.refl
  𝕀≅𝕀* .Iso.bwd .preserve-ze = S.refl
  𝕀≅𝕀* .Iso.bwd .preserve-+ = S.refl
  𝕀≅𝕀* .Iso.bwd .preserve-· = S.refl
  𝕀≅𝕀* .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq {φ} φ≈ψ .*≈* ._≈s_.func-eq {x} x≈y =
    S.trans S.·-comm
      (S.trans (S.sym (φ .preserve-· {x} {S.ι}))
        (φ≈ψ .*≈* ._≈s_.func-eq (S.trans (S.trans S.·-comm S.·-lunit) x≈y)))
  𝕀≅𝕀* .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq a≈b = S.trans (S.trans S.·-comm S.·-lunit) a≈b

  ------------------------------------------------------------------------------
  -- Dual preserves isomorphisms (contravariantly) and the zero object.

  Dual-iso : ∀ {M N} → Iso M N → Iso (Dual N) (Dual M)
  Dual-iso iso .Iso.fwd = (iso .Iso.fwd) ᵀ
  Dual-iso iso .Iso.bwd = (iso .Iso.bwd) ᵀ
  Dual-iso iso .Iso.fwd∘bwd≈id =
    ≈-trans (≈-sym (ᵀ-comp (iso .Iso.bwd) (iso .Iso.fwd))) (≈-trans (ᵀ-cong (iso .Iso.bwd∘fwd≈id)) ᵀ-id)
  Dual-iso iso .Iso.bwd∘fwd≈id =
    ≈-trans (≈-sym (ᵀ-comp (iso .Iso.fwd) (iso .Iso.bwd))) (≈-trans (ᵀ-cong (iso .Iso.fwd∘bwd≈id)) ᵀ-id)

  𝟘≅𝟘* : Iso SemiMod.𝟘 (Dual SemiMod.𝟘)
  𝟘≅𝟘* .Iso.fwd = εm
  𝟘≅𝟘* .Iso.bwd = HasTerminal.to-terminal SemiMod.terminal
  𝟘≅𝟘* .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq {_} {ψ} _ .*≈* ._≈s_.func-eq _ =
    sym SemiMod.𝕀 (trans SemiMod.𝕀 (ψ .func-resp-≈ tt) (ψ .preserve-ze))
  𝟘≅𝟘* .Iso.bwd∘fwd≈id = HasTerminal.to-terminal-unique SemiMod.terminal _ _

  Dual-⊕-iso : ∀ {M N} → Iso (Dual (M SemiMod.⊕ N)) (Dual M SemiMod.⊕ Dual N)
  Dual-⊕-iso {M} {N} = IsIso→Iso (biproduct-iso SemiMod.cmon-enriched Dual-preserves-⊕ (SemiMod.biproduct (Dual M) (Dual N)))

  ⊕-iso : ∀ {M M' N N'} → Iso M M' → Iso N N' → Iso (M SemiMod.⊕ N) (M' SemiMod.⊕ N')
  ⊕-iso = HasCoproducts.coproduct-preserve-iso (biproducts→coproducts SemiMod.cmon-enriched SemiMod.biproduct)

  -- The SemiMod.biproduct of two self-dualities is a self-duality of the SemiMod.biproduct.
  ⊕-self-dual : ∀ {M N} → Iso M (Dual M) → Iso N (Dual N) → Iso (M SemiMod.⊕ N) (Dual (M SemiMod.⊕ N))
  ⊕-self-dual M≅M* N≅N* = Iso-trans (⊕-iso M≅M* N≅N*) (Iso-sym Dual-⊕-iso)

  ⊕-iso-fwd : ∀ {M N} (M≅M* : Iso M (Dual M)) (N≅N* : Iso N (Dual N)) {x : M .Carrier} {y : N .Carrier} →
              (Dual M SemiMod.⊕ Dual N) ._≈_ (⊕-iso M≅M* N≅N* .Iso.fwd .func (x , y))
                                     (M≅M* .Iso.fwd .func x , N≅N* .Iso.fwd .func y)
  ⊕-iso-fwd {M} {N} M≅M* N≅N* .proj₁ = trans (Dual M) (+-comm (Dual M)) (+-lunit (Dual M))
  ⊕-iso-fwd {M} {N} M≅M* N≅N* .proj₂ = +-lunit (Dual N)

  pairing-⊕ : ∀ {M N} (M≅M* : Iso M (Dual M)) (N≅N* : Iso N (Dual N)) {x x' : M .Carrier} {y y' : N .Carrier} →
              pairing (⊕-self-dual M≅M* N≅N*) (x , y) (x' , y') S.≈ ((pairing M≅M* x x') S.+ (pairing N≅N* y y'))
  pairing-⊕ {M} {N} M≅M* N≅N* {x} {x'} {y} {y'} =
    S.trans (Dual-⊕-iso .Iso.bwd .func-resp-≈ (⊕-iso-fwd M≅M* N≅N* {x} {y}) .*≈* ._≈s_.func-eq (refl (M SemiMod.⊕ N)))
            S.refl

  ------------------------------------------------------------------------------
  -- Conjugate of a morphism w.r.t. chosen self-dualities d : M ≅ Dual M.

  module _ {M N} (M≅M* : Iso M (Dual M)) (N≅N* : Iso N (Dual N)) where

    conj : (M ⇒ N) → (N ⇒ M)
    conj f = M≅M* .Iso.bwd ∘ (f ᵀ ∘ N≅N* .Iso.fwd)

    conj-transpose : (f : M ⇒ N) → M≅M* .Iso.fwd ∘ conj f ≈m f ᵀ ∘ N≅N* .Iso.fwd
    conj-transpose f =
      ≈-trans (≈-sym (assoc (M≅M* .Iso.fwd) (M≅M* .Iso.bwd) (f ᵀ ∘ N≅N* .Iso.fwd)))
              (≈-trans (∘-cong (M≅M* .Iso.fwd∘bwd≈id) (≈-refl {f = f ᵀ ∘ N≅N* .Iso.fwd})) id-left)

    -- Pointwise conjugate equivalence ⟨ conj f y , x ⟩ ≈ ⟨ y , f x ⟩.
    conj-pairing : ∀ (f : M ⇒ N) {x y} →
                   pairing M≅M* (conj f .*→* ._⇒s_.func y) x S.≈ pairing N≅N* y (f .*→* ._⇒s_.func x)
    conj-pairing f =
      conj-transpose f .*≈* ._≈s_.func-eq (refl N) .*≈* ._≈s_.func-eq (refl M)

    -- conj swaps pairing-orthogonality: (⟨ y , f x ⟩ ≈ ε ⇔ ⟨ conj f y , x ⟩ ≈ ε).
    conj-⊥ : ∀ (f : M ⇒ N) {x y} →
             (pairing N≅N* y (f .*→* ._⇒s_.func x) S.≈ S.ε) ⇔ (pairing M≅M* (conj f .*→* ._⇒s_.func y) x S.≈ S.ε)
    conj-⊥ f .proj₁ p = S.trans (conj-pairing f) p
    conj-⊥ f .proj₂ q = S.trans (S.sym (conj-pairing f)) q

  ------------------------------------------------------------------------------
  -- Semimodule with a chosen self-duality.

  record SelfDual : Set (suc 0ℓ) where
    field
      obj  : Semimodule
      dual : Iso obj (Dual obj)
  -- local open so the obj/dual projections don't leak to SelfDualDistributiveLattice below.
  module _ where
    open SelfDual

    𝕀-sd : SelfDual
    𝕀-sd .obj = SemiMod.𝕀
    𝕀-sd .dual = 𝕀≅𝕀*

    𝟘-sd : SelfDual
    𝟘-sd .obj = SemiMod.𝟘
    𝟘-sd .dual = 𝟘≅𝟘*

    ⊕-sd : SelfDual → SelfDual → SelfDual
    ⊕-sd X Y .obj = X .obj SemiMod.⊕ Y .obj
    ⊕-sd X Y .dual = ⊕-self-dual (X .dual) (Y .dual)

    -- The conjugate of a morphism, with self-dualities read off the objects.
    conjugate : (X Y : SelfDual) → (X .obj ⇒ Y .obj) → (Y .obj ⇒ X .obj)
    conjugate X Y = conj (X .dual) (Y .dual)



open SelfDual

𝕀 : SelfDual
𝕀 = 𝕀-sd

𝟘 : SelfDual
𝟘 = 𝟘-sd

_⊕_ : SelfDual → SelfDual → SelfDual
_⊕_ = ⊕-sd

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = SelfDual
cat .Category._⇒_ X Y = X .obj ⇒ Y .obj
cat .Category._≈_ = _≈m_
cat .Category.isEquiv = SemiMod.cat .Category.isEquiv
cat .Category.id X = id (X .obj)
cat .Category._∘_ = _∘_
cat .Category.∘-cong = SemiMod.cat .Category.∘-cong
cat .Category.id-left = SemiMod.cat .Category.id-left
cat .Category.id-right = SemiMod.cat .Category.id-right
cat .Category.assoc = SemiMod.cat .Category.assoc

open CMonEnriched SemiMod.cmon-enriched
  using (homCM; εm; _+m_; comp-bilinear₁; comp-bilinear₂; comp-bilinear-ε₁; comp-bilinear-ε₂)
open CommutativeMonoid

cmon-enriched : CMonEnriched cat
cmon-enriched .CMonEnriched.homCM X Y .ε = εm
cmon-enriched .CMonEnriched.homCM X Y ._+_ = _+m_
cmon-enriched .CMonEnriched.homCM X Y .+-cong = homCM _ _ .+-cong
cmon-enriched .CMonEnriched.homCM X Y .+-lunit = homCM _ _ .+-lunit
cmon-enriched .CMonEnriched.homCM X Y .+-assoc = homCM _ _ .+-assoc
cmon-enriched .CMonEnriched.homCM X Y .+-comm = homCM _ _ .+-comm
cmon-enriched .CMonEnriched.comp-bilinear₁ = comp-bilinear₁
cmon-enriched .CMonEnriched.comp-bilinear₂ = comp-bilinear₂
cmon-enriched .CMonEnriched.comp-bilinear-ε₁ = comp-bilinear-ε₁
cmon-enriched .CMonEnriched.comp-bilinear-ε₂ = comp-bilinear-ε₂

terminal : HasTerminal cat
terminal .HasTerminal.witness = 𝟘
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X} =
  SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X .obj}
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext =
  SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext

biproduct : ∀ X Y → Biproduct cmon-enriched X Y
biproduct X Y .Biproduct.prod = X ⊕ Y
biproduct X Y .Biproduct.p₁ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.p₁
biproduct X Y .Biproduct.p₂ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.p₂
biproduct X Y .Biproduct.in₁ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.in₁
biproduct X Y .Biproduct.in₂ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.in₂
biproduct X Y .Biproduct.id-1 = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.id-1
biproduct X Y .Biproduct.id-2 = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.id-2
biproduct X Y .Biproduct.zero-1 = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.zero-1
biproduct X Y .Biproduct.zero-2 = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.zero-2
biproduct X Y .Biproduct.id-+ = SemiMod.biproduct (X .obj) (Y .obj) .Biproduct.id-+

products : HasProducts cat
products = biproducts→products cmon-enriched biproduct

-- Forgetful functor to SemiMod; full and faithful, so SDSemiMod is equivalent to the full subcategory of
-- SemiMod on the self-dualisable objects (objects for which some isomorphism to the dual exists).
U : Functor cat SemiMod.cat
U .Functor.fobj = SelfDual.obj
U .Functor.fmor f = f
U .Functor.fmor-cong f₁≈f₂ = f₁≈f₂
U .Functor.fmor-id = SemiMod.cat .Category.isEquiv .IsEquivalence.refl
U .Functor.fmor-comp f g = SemiMod.cat .Category.isEquiv .IsEquivalence.refl

private
  SemiMod-products : HasProducts SemiMod.cat
  SemiMod-products = biproducts→products SemiMod.cmon-enriched SemiMod.biproduct

open Category SemiMod.cat using (IsIso; ≈-refl; ≈-trans; ≈-sym; id-left; id-right; ∘-cong)
open IsTerminal (SemiMod.terminal .HasTerminal.is-terminal) using (to-terminal; to-terminal-unique)
open HasProducts SemiMod-products using (pair; p₁; p₂; pair-natural; pair-ext)
open finite-product-functor U using (preserve-chosen-terminal; preserve-chosen-products)

U-preserve-terminal : preserve-chosen-terminal terminal SemiMod.terminal
U-preserve-terminal .IsIso.inverse = to-terminal
U-preserve-terminal .IsIso.f∘inverse≈id = to-terminal-unique _ _
U-preserve-terminal .IsIso.inverse∘f≈id = to-terminal-unique _ _

U-preserve-products : preserve-chosen-products products SemiMod-products
U-preserve-products {X} {Y} .IsIso.inverse = id ((X .obj) SemiMod.⊕ (Y .obj))
U-preserve-products {X} {Y} .IsIso.f∘inverse≈id =
  ≈-trans (pair-natural (id ((X .obj) SemiMod.⊕ (Y .obj))) p₁ p₂)
    (pair-ext (id ((X .obj) SemiMod.⊕ (Y .obj))))
U-preserve-products {X} {Y} .IsIso.inverse∘f≈id = ≈-trans id-left pair-p≈id
  where
    pair-p≈id : pair (p₁ {X .obj} {Y .obj}) (p₂ {X .obj} {Y .obj}) ≈m id ((X .obj) SemiMod.⊕ (Y .obj))
    pair-p≈id =
      ≈-trans (≈-sym id-right)
        (≈-trans (pair-natural (id ((X .obj) SemiMod.⊕ (Y .obj))) p₁ p₂)
          (pair-ext (id ((X .obj) SemiMod.⊕ (Y .obj)))))

-- 𝟘 is also initial: any map out of it is the zero map, since id on 𝟘 is the zero map.
initial : HasInitial cat
initial .HasInitial.witness = 𝟘
initial .HasInitial.is-initial .IsInitial.from-initial = εm
initial .HasInitial.is-initial .IsInitial.from-initial-ext f =
  ≈-sym (≈-trans (≈-sym id-right)
    (≈-trans (∘-cong (≈-refl {f = f}) (to-terminal-unique (id (𝟘 .obj)) εm))
      (comp-bilinear-ε₂ f)))

------------------------------------------------------------------------------
private module S = SemiMod.S

-- With S a bounded distributive lattice (join +, meet ·), a self-dual semimodule whose induced
-- join-semilattice extends to a distributive lattice, such that lattice-level disjointness agrees
-- with semimodule-level orthogonality.
module DistributiveLattices
  (⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι)
  (∧-idem    : ∀ {x} → (x S.· x) S.≈ x)
  where

  open import basics using (IsPreorder; IsMeet; IsTop; module Disjoint)
  open import meet-semilattice using (MeetSemilattice)
  open import join-semilattice using (JoinSemilattice)
  open import lattice using (DistributiveLattice)
  open import conjugate using (_⇒c_)
  open import prop using (proj₁; proj₂; tt; _⇔_; trans-⇔; sym-⇔; _,_)
  open import Data.Product using (_,_)
  open SemiMod using (Semimodule)
  open SemiMod.JoinSemilattices ⊤-add-top
    using (preorder; _≤_; ≈→≤; joins; joins-map; zero-sum-free; ≤-isPreorder)

  record SelfDualDistributiveLattice : Set (suc 0ℓ) where
    no-eta-equality
    field
      selfDual : SelfDual
    open SelfDual selfDual public

    field
      meets : MeetSemilattice (preorder (selfDual .SelfDual.obj))

    open MeetSemilattice meets using (_∧_)
    open JoinSemilattice (joins (selfDual .SelfDual.obj)) using (_∨_)
    open Disjoint (≤-isPreorder (selfDual .SelfDual.obj)) (MeetSemilattice.∧-isMeet meets)
      (JoinSemilattice.⊥-isBottom (joins (selfDual .SelfDual.obj))) using (_#_)

    field
      ∧-∨-distrib : ∀ x y z → _≤_ (selfDual .SelfDual.obj) (x ∧ (y ∨ z)) ((x ∧ y) ∨ (x ∧ z))
      align       : ∀ {a b} → (a # b) ⇔ (pairing (selfDual .SelfDual.dual) a b S.≈ S.ε)

  -- Embedding of objects into LatConj.
    toObj : DistributiveLattice
    toObj .DistributiveLattice.carrier     = preorder (selfDual .SelfDual.obj)
    toObj .DistributiveLattice.meets       = meets
    toObj .DistributiveLattice.joins       = joins (selfDual .SelfDual.obj)
    toObj .DistributiveLattice.∧-∨-distrib = ∧-∨-distrib

  -- Embedding of morphisms into LatConj.
  module _ (X Y : SelfDualDistributiveLattice) where
    private
      module X = SelfDualDistributiveLattice X
      module Y = SelfDualDistributiveLattice Y
      module MX = MeetSemilattice X.meets
      module MY = MeetSemilattice Y.meets

    -- Componentwise meet on the biproduct (the meet-semilattice product, but indexed by preorder (X.obj ⊕ Y.obj)).
    meets-⊕ : MeetSemilattice (preorder ((X.obj) SemiMod.⊕ (Y.obj)))
    meets-⊕ .MeetSemilattice._∧_ (x₁ , y₁) (x₂ , y₂) = MX._∧_ x₁ x₂ , MY._∧_ y₁ y₂
    meets-⊕ .MeetSemilattice.⊤ = MX.⊤ , MY.⊤
    meets-⊕ .MeetSemilattice.∧-isMeet .IsMeet.π₁ = MX.∧-isMeet .IsMeet.π₁ , MY.∧-isMeet .IsMeet.π₁
    meets-⊕ .MeetSemilattice.∧-isMeet .IsMeet.π₂ = MX.∧-isMeet .IsMeet.π₂ , MY.∧-isMeet .IsMeet.π₂
    meets-⊕ .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ (x₁≤y₁ , x₂≤y₂) (x₁≤z₁ , x₂≤z₂) =
      MX.∧-isMeet .IsMeet.⟨_,_⟩ x₁≤y₁ x₁≤z₁ , MY.∧-isMeet .IsMeet.⟨_,_⟩ x₂≤y₂ x₂≤z₂
    meets-⊕ .MeetSemilattice.⊤-isTop .IsTop.≤-top = MX.⊤-isTop .IsTop.≤-top , MY.⊤-isTop .IsTop.≤-top

    ⊕-lattice : SelfDualDistributiveLattice
    ⊕-lattice .SelfDualDistributiveLattice.selfDual    = ⊕-sd X.selfDual Y.selfDual
    ⊕-lattice .SelfDualDistributiveLattice.meets       = meets-⊕
    ⊕-lattice .SelfDualDistributiveLattice.∧-∨-distrib (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) =
      X.∧-∨-distrib x₁ y₁ z₁ , Y.∧-∨-distrib x₂ y₂ z₂
    ⊕-lattice .SelfDualDistributiveLattice.align {x₁ , x₂} {y₁ , y₂} .proj₁ (d₁ , d₂) =
      S.trans (pairing-⊕ X.dual Y.dual)
              (S.trans (S.+-cong (X.align .proj₁ d₁) (Y.align .proj₁ d₂)) S.+-lunit)
    ⊕-lattice .SelfDualDistributiveLattice.align {x₁ , x₂} {y₁ , y₂} .proj₂ h =
      let p₁ , p₂ = zero-sum-free SemiMod.𝕀 (S.trans (S.sym (pairing-⊕ X.dual Y.dual)) h)
      in X.align .proj₂ p₁ , Y.align .proj₂ p₂

    to-conj : (X.obj) ⇒ (Y.obj) → X.toObj ⇒c Y.toObj
    to-conj f ._⇒c_.right = joins-map f
    to-conj f ._⇒c_.left = joins-map (conjugate X.selfDual Y.selfDual f)
    to-conj f ._⇒c_.conjugate =
      trans-⇔ Y.align (trans-⇔ (conj-⊥ X.dual Y.dual f) (sym-⇔ X.align))

  -- 𝕀 is a self-dual distributive lattice, with multiplication as the meet.
  private
    ∨-∧-absorption : ∀ {a b} → (a S.+ (a S.· b)) S.≈ a
    ∨-∧-absorption =
      S.trans (S.+-cong (S.trans (S.sym S.·-lunit) S.·-comm) S.refl)
              (S.trans (S.sym S.·-+-distribₗ)
                       (S.trans (S.·-cong S.refl ⊤-add-top) (S.trans S.·-comm S.·-lunit)))

    ∧-monoʳ : ∀ {a b c} → _≤_ SemiMod.𝕀 a b → _≤_ SemiMod.𝕀 (c S.· a) (c S.· b)
    ∧-monoʳ a≤b = S.trans (S.sym S.·-+-distribₗ) (S.·-cong S.refl a≤b)

    ∧-monoˡ : ∀ {a b c} → _≤_ SemiMod.𝕀 a b → _≤_ SemiMod.𝕀 (a S.· c) (b S.· c)
    ∧-monoˡ a≤b = S.trans (S.sym S.·-+-distribᵣ) (S.·-cong a≤b S.refl)

  𝕀-meet : MeetSemilattice (preorder SemiMod.𝕀)
  𝕀-meet .MeetSemilattice._∧_ = S._·_
  𝕀-meet .MeetSemilattice.⊤ = S.ι
  𝕀-meet .MeetSemilattice.∧-isMeet .IsMeet.π₁ = S.trans S.+-comm ∨-∧-absorption
  𝕀-meet .MeetSemilattice.∧-isMeet .IsMeet.π₂ =
    S.trans (S.+-cong S.·-comm S.refl) (S.trans S.+-comm ∨-∧-absorption)
  𝕀-meet .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z =
    ≤-isPreorder SemiMod.𝕀 .IsPreorder.trans
      (S.trans (S.+-cong (S.sym ∧-idem) S.refl) (∧-monoʳ x≤z)) (∧-monoˡ x≤y)
  𝕀-meet .MeetSemilattice.⊤-isTop .IsTop.≤-top = S.trans S.+-comm ⊤-add-top

  𝕀-lattice : SelfDualDistributiveLattice
  𝕀-lattice .SelfDualDistributiveLattice.selfDual    = 𝕀-sd
  𝕀-lattice .SelfDualDistributiveLattice.meets       = 𝕀-meet
  𝕀-lattice .SelfDualDistributiveLattice.∧-∨-distrib x y z = ≈→≤ SemiMod.𝕀 S.·-+-distribₗ
  𝕀-lattice .SelfDualDistributiveLattice.align .proj₁ h = S.trans (S.sym (S.trans S.+-comm S.+-lunit)) h
  𝕀-lattice .SelfDualDistributiveLattice.align .proj₂ h = ≈→≤ SemiMod.𝕀 h

  -- 𝟘 is trivially a self-dual distributive lattice.
  𝟘-lattice : SelfDualDistributiveLattice
  𝟘-lattice .SelfDualDistributiveLattice.selfDual                                   = 𝟘-sd
  𝟘-lattice .SelfDualDistributiveLattice.meets .MeetSemilattice._∧_ _ _             = Semimodule.ε SemiMod.𝟘
  𝟘-lattice .SelfDualDistributiveLattice.meets .MeetSemilattice.⊤                   = Semimodule.ε SemiMod.𝟘
  𝟘-lattice .SelfDualDistributiveLattice.meets .MeetSemilattice.∧-isMeet .IsMeet.π₁ = tt
  𝟘-lattice .SelfDualDistributiveLattice.meets .MeetSemilattice.∧-isMeet .IsMeet.π₂ = tt
  𝟘-lattice .SelfDualDistributiveLattice.meets .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ _ _ = tt
  𝟘-lattice .SelfDualDistributiveLattice.meets .MeetSemilattice.⊤-isTop .IsTop.≤-top = tt
  𝟘-lattice .SelfDualDistributiveLattice.∧-∨-distrib _ _ _                          = tt
  𝟘-lattice .SelfDualDistributiveLattice.align .proj₁ _                             = S.refl
  𝟘-lattice .SelfDualDistributiveLattice.align .proj₂ _                             = tt
