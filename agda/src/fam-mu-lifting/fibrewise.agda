{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The change of base along a structured functor commutes with the μ-carriers.
-- The change of base keeps index setoids, and sorts and trees are built from
-- index setoids alone, so the two μ-carriers share their trees up to a
-- transport that is the identity at the leaves. The fibre comparison is by
-- recursion on trees: constants and parameters are untouched, products cross
-- the base functor's product comparison, and each root crosses its lifting
-- comparison, whose naturality at the lifted action carries the transports.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ) renaming (suc to sucℕ)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using () renaming (_,_ to _,ₚ_)
open import categories using (Category; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
import lifting
open import functor using (Functor; functor-preserve-iso)
open import finite-product-functor
  using (preserve-chosen-products; module preserve-chosen-products-consequences)
open import prop-setoid using (Setoid; IsEquivalence; mk-≃m)
open import indexed-family using (Fam)
import fam
import fam-functor
import polynomial-functor
import fam-mu-lifting.sort
import fam-mu-lifting.fibre

module fam-mu-lifting.fibrewise {o m e o₂ m₂ e₂} (os es : Level)
    {𝒞 : Category o m e} (CM𝒞 : CMonEnriched 𝒞) (BP𝒞 : ∀ x y → Biproduct CM𝒞 x y)
    (𝟙𝒞 : Category.obj 𝒞)
    {𝒟 : Category o₂ m₂ e₂} (CM𝒟 : CMonEnriched 𝒟) (BP𝒟 : ∀ x y → Biproduct CM𝒟 x y)
    (𝟙𝒟 : Category.obj 𝒟)
    (F : Functor 𝒞 𝒟)
    (F-prod : preserve-chosen-products F (biproducts→products CM𝒞 BP𝒞) (biproducts→products CM𝒟 BP𝒟))
    (let module L𝒞 = lifting CM𝒞 BP𝒞 𝟙𝒞) (let module L𝒟 = lifting CM𝒟 BP𝒟 𝟙𝒟)
    (let module 𝒞 = Category 𝒞) (let module 𝒟 = Category 𝒟) (let open Functor)
    (F-L : ∀ X → 𝒟.Iso (fobj F (L𝒞.L X)) (L𝒟.L (fobj F X)))
    (F-L-natural : ∀ {X Y} (f : X 𝒞.⇒ Y) →
       (F-L Y .𝒟.Iso.fwd 𝒟.∘ fmor F (L𝒞.Lmap f))
         𝒟.≈ (L𝒟.Lmap (fmor F f) 𝒟.∘ F-L X .𝒟.Iso.fwd))
    where

private
  module F𝒞 = fam.CategoryOfFamilies os (os ⊔ es) 𝒞
  module F𝒟 = fam.CategoryOfFamilies os (os ⊔ es) 𝒟
  module F𝒟-cat = Category F𝒟.cat
  module sort = fam-mu-lifting.sort os es
  module Fib𝒞 = fam-mu-lifting.fibre os es CM𝒞 BP𝒞 𝟙𝒞
  module Fib𝒟 = fam-mu-lifting.fibre os es CM𝒟 BP𝒟 𝟙𝒟

open HasProducts (biproducts→products CM𝒟 BP𝒟)
  using (prod-m-comp; prod-m-cong; product-preserves-iso)
open sort using (Sort; mkSort)
open polynomial-functor using (Poly; Poly-map; extend)
open prop-setoid._⇒_
open Functor
open F𝒞.Obj
open F𝒟.Obj
open F𝒟.Mor
open F𝒟._≃_
open indexed-family._⇒f_
open indexed-family._≃f_
open 𝒟
open Iso

FamF : Functor F𝒞.cat F𝒟.cat
FamF = fam-functor.FamF os (os ⊔ es) F

private
  L-iso : ∀ {a b} → 𝒟.Iso a b → 𝒟.Iso (L𝒟.L a) (L𝒟.L b)
  L-iso = functor-preserve-iso L𝒟.L-functor

  iso-flip : ∀ {a b c d} (i : 𝒟.Iso a b) (j : 𝒟.Iso c d)
             {f : a ⇒ c} {g : b ⇒ d} →
             (j .fwd ∘ f) ≈ (g ∘ i .fwd) →
             (f ∘ i .bwd) ≈ (j .bwd ∘ g)
  iso-flip i j {f} {g} sq =
    ≈-trans (≈-sym id-left)
      (≈-trans (∘-cong (≈-sym (j .bwd∘fwd≈id)) ≈-refl)
        (tail-cong (≈-trans (head-cong sq)
                    (tail-cancel (i .fwd∘bwd≈id)))))

  root-step : ∀ {a a' b b'} (i' : 𝒟.Iso (F .fobj a') b') (i : 𝒟.Iso (F .fobj a) b)
              {s : a 𝒞.⇒ a'} {t : b ⇒ b'} →
              ((i' .fwd ∘ F .fmor s) ≈ (t ∘ i .fwd)) →
              (((L𝒟.Lmap (i' .fwd) ∘ F-L a' .fwd) ∘ F .fmor (L𝒞.Lmap s))
                ≈ (L𝒟.Lmap t ∘ (L𝒟.Lmap (i .fwd) ∘ F-L a .fwd)))
  root-step {a} {a'} i' i {s} {t} inner =
    ≈-trans (tail-cong (F-L-natural s))
    (head-cong-assoc (≈-trans (≈-sym (L𝒟.Lmap-comp _ _))
                       (≈-trans (L𝒟.Lmap-cong inner) (L𝒟.Lmap-comp _ _))))

ℓk : Level
ℓk = o ⊔ m ⊔ e ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ lsuc os ⊔ lsuc es

module Fibrewise {N : ℕ} (δ : Fin N → F𝒞.Obj) where
  open sort.Tree (λ i → δ i .idx) public
    using (W; W-≈; W-≈-sym; El; elEq; elEq-refl; sup; shape≈; ⟦_⟧shape)
  module Fibre𝒞 = Fib𝒞.Fibre δ
  module Fibre𝒟 = Fib𝒟.Fibre (λ i → FamF .fobj (δ i))

  P̂ : ∀ {j} → Fib𝒞.Poly-C j → Fib𝒟.Poly-C j
  P̂ = Poly-map FamF

  mutual
    record RelAssign (j : ℕ) : Set ℓk where
      inductive
      field
        ρ₁  : Fin j → Fin N ⊎ Sort N
        ρ₂  : Fin j → Fin N ⊎ Sort N
        d₁  : ∀ i → Fibre𝒞.DecoAssign (ρ₁ i)
        d₂  : ∀ i → Fibre𝒟.DecoAssign (ρ₂ i)
        rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)

    data SRel : (r₁ r₂ : Fin N ⊎ Sort N) → Fibre𝒞.DecoAssign r₁ → Fibre𝒟.DecoAssign r₂ → Set ℓk where
      env : ∀ {p} → SRel (inj₁ p) (inj₁ p) (lift tt) (lift tt)
      srt : ∀ {s₁ s₂ e₁ e₂} → SortRel s₁ s₂ e₁ e₂ → SRel (inj₂ s₁) (inj₂ s₂) e₁ e₂

    data SortRel : (s₁ s₂ : Sort N) → Fibre𝒞.Deco s₁ → Fibre𝒟.Deco s₂ → Set ℓk where
      mk : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
           SortRel (mkSort Fib𝒞.∣ Q ∣ (E .RelAssign.ρ₁)) (mkSort Fib𝒟.∣ P̂ Q ∣ (E .RelAssign.ρ₂))
                   (Fibre𝒞.mkDeco Q (E .RelAssign.d₁)) (Fibre𝒟.mkDeco (P̂ Q) (E .RelAssign.d₂))

  open RelAssign public

  ext : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) → RelAssign j → RelAssign (sucℕ j)
  ext Q E .ρ₁ = extend (E .ρ₁) (inj₂ (mkSort Fib𝒞.∣ Q ∣ (E .ρ₁)))
  ext Q E .ρ₂ = extend (E .ρ₂) (inj₂ (mkSort Fib𝒟.∣ P̂ Q ∣ (E .ρ₂)))
  ext Q E .d₁ = Fibre𝒞.deco-ext Q (E .d₁)
  ext Q E .d₂ = Fibre𝒟.deco-ext (P̂ Q) (E .d₂)
  ext Q E .rel Fin.zero    = srt (mk Q E)
  ext Q E .rel (Fin.suc i) = E .rel i

  mutual
    cmp-fwd : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
           W Fib𝒞.∣ Q ∣ (E .ρ₁) → W Fib𝒟.∣ P̂ Q ∣ (E .ρ₂)
    cmp-fwd Q E (sup x) = sup (shape-cmp-fwd Q (ext Q E) x)

    shape-cmp-fwd : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j) →
                 ⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁) → ⟦ Fib𝒟.∣ P̂ Q ∣ ⟧shape (E .ρ₂)
    shape-cmp-fwd (Poly.const A) E x = x
    shape-cmp-fwd (Poly.var i)   E x = el-cmp-fwd (E .rel i) x
    shape-cmp-fwd (Q Poly.+ R) E (inj₁ x) = inj₁ (shape-cmp-fwd Q E x)
    shape-cmp-fwd (Q Poly.+ R) E (inj₂ y) = inj₂ (shape-cmp-fwd R E y)
    shape-cmp-fwd (Q Poly.× R) E (x , y) = shape-cmp-fwd Q E x , shape-cmp-fwd R E y
    shape-cmp-fwd (Poly.μ Q')  E t = cmp-fwd Q' E t

    el-cmp-fwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → El r₁ → El r₂
    el-cmp-fwd env x = x
    el-cmp-fwd (srt (mk Q E)) x = cmp-fwd Q E x

  mutual
    c≈fwd : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
            {x y : W Fib𝒞.∣ Q ∣ (E .ρ₁)} → W-≈ x y →
            W-≈ (cmp-fwd Q E x) (cmp-fwd Q E y)
    c≈fwd Q E {sup x} {sup y} p = shape≈-cmp-fwd Q (ext Q E) p

    shape≈-cmp-fwd : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j) →
                  {x y : ⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)} → shape≈ Fib𝒞.∣ Q ∣ (E .ρ₁) x y →
                  shape≈ Fib𝒟.∣ P̂ Q ∣ (E .ρ₂) (shape-cmp-fwd Q E x) (shape-cmp-fwd Q E y)
    shape≈-cmp-fwd (Poly.const A) E p = p
    shape≈-cmp-fwd (Poly.var i)   E p = elEq-cmp-fwd (E .rel i) p
    shape≈-cmp-fwd (Q Poly.+ R) E {inj₁ _} {inj₁ _} p = shape≈-cmp-fwd Q E p
    shape≈-cmp-fwd (Q Poly.+ R) E {inj₂ _} {inj₂ _} p = shape≈-cmp-fwd R E p
    shape≈-cmp-fwd (Q Poly.× R) E {_ , _} {_ , _} (p ,ₚ q) = shape≈-cmp-fwd Q E p ,ₚ shape≈-cmp-fwd R E q
    shape≈-cmp-fwd (Poly.μ Q')  E {x} {y} p = c≈fwd Q' E {x} {y} p

    elEq-cmp-fwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : El r₁} →
                elEq r₁ x y → elEq r₂ (el-cmp-fwd r x) (el-cmp-fwd r y)
    elEq-cmp-fwd env p = p
    elEq-cmp-fwd (srt (mk Q E)) {x} {y} p = c≈fwd Q E {x} {y} p

  mutual
    cmp-bwd : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
           W Fib𝒟.∣ P̂ Q ∣ (E .ρ₂) → W Fib𝒞.∣ Q ∣ (E .ρ₁)
    cmp-bwd Q E (sup x) = sup (shape-cmp-bwd Q (ext Q E) x)

    shape-cmp-bwd : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j) →
                 ⟦ Fib𝒟.∣ P̂ Q ∣ ⟧shape (E .ρ₂) → ⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)
    shape-cmp-bwd (Poly.const A) E x = x
    shape-cmp-bwd (Poly.var i)   E x = el-cmp-bwd (E .rel i) x
    shape-cmp-bwd (Q Poly.+ R) E (inj₁ x) = inj₁ (shape-cmp-bwd Q E x)
    shape-cmp-bwd (Q Poly.+ R) E (inj₂ y) = inj₂ (shape-cmp-bwd R E y)
    shape-cmp-bwd (Q Poly.× R) E (x , y) = shape-cmp-bwd Q E x , shape-cmp-bwd R E y
    shape-cmp-bwd (Poly.μ Q')  E t = cmp-bwd Q' E t

    el-cmp-bwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → El r₂ → El r₁
    el-cmp-bwd env x = x
    el-cmp-bwd (srt (mk Q E)) x = cmp-bwd Q E x

  mutual
    c≈bwd : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
            {x y : W Fib𝒟.∣ P̂ Q ∣ (E .ρ₂)} → W-≈ x y →
            W-≈ (cmp-bwd Q E x) (cmp-bwd Q E y)
    c≈bwd Q E {sup x} {sup y} p = shape≈-cmp-bwd Q (ext Q E) p

    shape≈-cmp-bwd : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j) →
                  {x y : ⟦ Fib𝒟.∣ P̂ Q ∣ ⟧shape (E .ρ₂)} → shape≈ Fib𝒟.∣ P̂ Q ∣ (E .ρ₂) x y →
                  shape≈ Fib𝒞.∣ Q ∣ (E .ρ₁) (shape-cmp-bwd Q E x) (shape-cmp-bwd Q E y)
    shape≈-cmp-bwd (Poly.const A) E p = p
    shape≈-cmp-bwd (Poly.var i)   E p = elEq-cmp-bwd (E .rel i) p
    shape≈-cmp-bwd (Q Poly.+ R) E {inj₁ _} {inj₁ _} p = shape≈-cmp-bwd Q E p
    shape≈-cmp-bwd (Q Poly.+ R) E {inj₂ _} {inj₂ _} p = shape≈-cmp-bwd R E p
    shape≈-cmp-bwd (Q Poly.× R) E {_ , _} {_ , _} (p ,ₚ q) = shape≈-cmp-bwd Q E p ,ₚ shape≈-cmp-bwd R E q
    shape≈-cmp-bwd (Poly.μ Q')  E {x} {y} p = c≈bwd Q' E {x} {y} p

    elEq-cmp-bwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : El r₂} →
                elEq r₂ x y → elEq r₁ (el-cmp-bwd r x) (el-cmp-bwd r y)
    elEq-cmp-bwd env p = p
    elEq-cmp-bwd (srt (mk Q E)) {x} {y} p = c≈bwd Q E {x} {y} p

  mutual
    cmp-fb : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j)
           (x : W Fib𝒞.∣ Q ∣ (E .ρ₁)) →
           W-≈ (cmp-bwd Q E (cmp-fwd Q E x)) x
    cmp-fb Q E (sup x) = shape-cmp-fb Q (ext Q E) x

    shape-cmp-fb : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j)
                (x : ⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)) →
                shape≈ Fib𝒞.∣ Q ∣ (E .ρ₁) (shape-cmp-bwd Q E (shape-cmp-fwd Q E x)) x
    shape-cmp-fb (Poly.const A) E x = IsEquivalence.refl (Setoid.isEquivalence (A .idx))
    shape-cmp-fb (Poly.var i)   E x = el-cmp-fb (E .rel i) x
    shape-cmp-fb (Q Poly.+ R) E (inj₁ x) = shape-cmp-fb Q E x
    shape-cmp-fb (Q Poly.+ R) E (inj₂ y) = shape-cmp-fb R E y
    shape-cmp-fb (Q Poly.× R) E (x , y) = shape-cmp-fb Q E x ,ₚ shape-cmp-fb R E y
    shape-cmp-fb (Poly.μ Q')  E t = cmp-fb Q' E t

    el-cmp-fb : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : El r₁) → elEq r₁ (el-cmp-bwd r (el-cmp-fwd r x)) x
    el-cmp-fb (env {p}) x = elEq-refl (inj₁ p) x
    el-cmp-fb (srt (mk Q E)) x = cmp-fb Q E x

  mutual
    cmp-bf : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j)
           (y : W Fib𝒟.∣ P̂ Q ∣ (E .ρ₂)) →
           W-≈ (cmp-fwd Q E (cmp-bwd Q E y)) y
    cmp-bf Q E (sup y) = shape-cmp-bf Q (ext Q E) y

    shape-cmp-bf : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j)
                (y : ⟦ Fib𝒟.∣ P̂ Q ∣ ⟧shape (E .ρ₂)) →
                shape≈ Fib𝒟.∣ P̂ Q ∣ (E .ρ₂) (shape-cmp-fwd Q E (shape-cmp-bwd Q E y)) y
    shape-cmp-bf (Poly.const A) E y = IsEquivalence.refl (Setoid.isEquivalence (A .idx))
    shape-cmp-bf (Poly.var i)   E y = el-cmp-bf (E .rel i) y
    shape-cmp-bf (Q Poly.+ R) E (inj₁ y) = shape-cmp-bf Q E y
    shape-cmp-bf (Q Poly.+ R) E (inj₂ y) = shape-cmp-bf R E y
    shape-cmp-bf (Q Poly.× R) E (x , y) = shape-cmp-bf Q E x ,ₚ shape-cmp-bf R E y
    shape-cmp-bf (Poly.μ Q')  E t = cmp-bf Q' E t

    el-cmp-bf : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (y : El r₂) → elEq r₂ (el-cmp-fwd r (el-cmp-bwd r y)) y
    el-cmp-bf (env {p}) y = elEq-refl (inj₁ p) y
    el-cmp-bf (srt (mk Q E)) y = cmp-bf Q E y

  mutual
    fib-cmp-iso : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j)
               (w : W Fib𝒞.∣ Q ∣ (E .ρ₁)) →
               𝒟.Iso (F .fobj (Fibre𝒞.fib Q (E .d₁) w)) (Fibre𝒟.fib (P̂ Q) (E .d₂) (cmp-fwd Q E w))
    fib-cmp-iso Q E (sup x) = fib-shape-cmp-iso Q (ext Q E) x

    fib-shape-cmp-iso : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j)
                     (x : ⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)) →
                     𝒟.Iso (F .fobj (Fibre𝒞.fib-shape Q (E .d₁) x))
                            (Fibre𝒟.fib-shape (P̂ Q) (E .d₂) (shape-cmp-fwd Q E x))
    fib-shape-cmp-iso (Poly.const A) E x = Iso-refl
    fib-shape-cmp-iso (Poly.var i)   E x = fib-el-cmp-iso (E .rel i) x
    fib-shape-cmp-iso (Q Poly.+ R) E (inj₁ x) = Iso-trans (F-L _) (L-iso (fib-shape-cmp-iso Q E x))
    fib-shape-cmp-iso (Q Poly.+ R) E (inj₂ y) = Iso-trans (F-L _) (L-iso (fib-shape-cmp-iso R E y))
    fib-shape-cmp-iso (Q Poly.× R) E (x , y) =
      Iso-trans (F-L _)
        (L-iso (Iso-trans (IsIso→Iso F-prod)
                 (product-preserves-iso
                   (fib-shape-cmp-iso Q E x)
                   (fib-shape-cmp-iso R E y))))
    fib-shape-cmp-iso (Poly.μ Q')  E t = fib-cmp-iso Q' E t

    fib-el-cmp-iso : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : El r₁) →
                  𝒟.Iso (F .fobj (Fibre𝒞.fib-el r₁ e₁ x)) (Fibre𝒟.fib-el r₂ e₂ (el-cmp-fwd r x))
    fib-el-cmp-iso (env {p}) x = Iso-refl
    fib-el-cmp-iso (srt (mk Q E)) x = fib-cmp-iso Q E x

  open preserve-chosen-products-consequences F (biproducts→products CM𝒞 BP𝒞) (biproducts→products CM𝒟 BP𝒟) F-prod
    using (mul⁻¹-natural)

  mutual
    fib-cmp-nat : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j)
               {w w' : W Fib𝒞.∣ Q ∣ (E .ρ₁)} (p : W-≈ w w') →
               ((fib-cmp-iso Q E w' .fwd)
                 ∘ F .fmor (Fibre𝒞.fib-subst Q (E .d₁) {x = w} {y = w'} p))
               ≈ ((Fibre𝒟.fib-subst (P̂ Q) (E .d₂)
                        {x = cmp-fwd Q E w} {y = cmp-fwd Q E w'}
                        (c≈fwd Q E {w} {w'} p))
                     ∘ (fib-cmp-iso Q E w .fwd))
    fib-cmp-nat Q E {sup x} {sup x'} p = fib-shape-cmp-nat Q (ext Q E) {x} {x'} p

    fib-shape-cmp-nat : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j)
                     {x x' : ⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)} (p : shape≈ Fib𝒞.∣ Q ∣ (E .ρ₁) x x') →
                     ((fib-shape-cmp-iso Q E x' .fwd)
                       ∘ F .fmor (Fibre𝒞.fib-shape-subst Q (E .d₁) p))
                     ≈ ((Fibre𝒟.fib-shape-subst (P̂ Q) (E .d₂) (shape≈-cmp-fwd Q E {x} {x'} p))
                           ∘ (fib-shape-cmp-iso Q E x .fwd))
    fib-shape-cmp-nat (Poly.const A) E p = ≈-trans id-left (≈-sym id-right)
    fib-shape-cmp-nat (Poly.var i)   E p = fib-el-cmp-nat (E .rel i) p
    fib-shape-cmp-nat (Q Poly.+ R) E {inj₁ x} {inj₁ x'} p =
      root-step (fib-shape-cmp-iso Q E x') (fib-shape-cmp-iso Q E x)
        (fib-shape-cmp-nat Q E p)
    fib-shape-cmp-nat (Q Poly.+ R) E {inj₂ y} {inj₂ y'} p =
      root-step (fib-shape-cmp-iso R E y') (fib-shape-cmp-iso R E y)
        (fib-shape-cmp-nat R E p)
    fib-shape-cmp-nat (Q Poly.× R) E {x₁ , x₂} {x₁' , x₂'} (p₁ ,ₚ p₂) =
      root-step pI' pI
        (≈-trans (tail-cong (mul⁻¹-natural {f = s₁} {g = s₂}))
         (head-cong-assoc (≈-trans (≈-sym (prod-m-comp _ _ _ _))
                            (≈-trans
                              (prod-m-cong
                                (fib-shape-cmp-nat Q E {x₁} {x₁'} p₁)
                                (fib-shape-cmp-nat R E {x₂} {x₂'} p₂))
                              (prod-m-comp _ _ _ _)))))
      where
        s₁ = Fibre𝒞.fib-shape-subst Q (E .d₁) p₁
        s₂ = Fibre𝒞.fib-shape-subst R (E .d₁) p₂

        pI : 𝒟.Iso _ _
        pI = Iso-trans (IsIso→Iso F-prod)
               (product-preserves-iso
                 (fib-shape-cmp-iso Q E x₁)
                 (fib-shape-cmp-iso R E x₂))

        pI' : 𝒟.Iso _ _
        pI' = Iso-trans (IsIso→Iso F-prod)
                (product-preserves-iso
                  (fib-shape-cmp-iso Q E x₁')
                  (fib-shape-cmp-iso R E x₂'))
    fib-shape-cmp-nat (Poly.μ Q')  E {t} {t'} p = fib-cmp-nat Q' E {t} {t'} p

    fib-el-cmp-nat : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x x' : El r₁} (p : elEq r₁ x x') →
                  ((fib-el-cmp-iso r x' .fwd)
                    ∘ F .fmor (Fibre𝒞.fib-el-subst r₁ e₁ p))
                  ≈ ((Fibre𝒟.fib-el-subst r₂ e₂ (elEq-cmp-fwd r {x} {x'} p))
                        ∘ (fib-el-cmp-iso r x .fwd))
    fib-el-cmp-nat (env {p}) q = ≈-trans id-left (≈-sym id-right)
    fib-el-cmp-nat (srt (mk Q E)) {x} {x'} q = fib-cmp-nat Q E {x} {x'} q

module FibrewiseMu {n : ℕ} (P : Fib𝒞.Poly-C (sucℕ n)) (δ : Fin n → F𝒞.Obj) where
  open Fibrewise δ
  open Fam

  private
    E₀ : RelAssign n
    E₀ .ρ₁ i = inj₁ i
    E₀ .ρ₂ i = inj₁ i
    E₀ .d₁ i = lift tt
    E₀ .d₂ i = lift tt
    E₀ .rel i = env

    Fw = cmp-fwd P E₀
    Bw = cmp-bwd P E₀
    ci = fib-cmp-iso P E₀

  fwd-mor : F𝒟.Mor (FamF .fobj (Fib𝒞.μ-fam P δ)) (Fib𝒟.μ-fam (P̂ P) (λ i → FamF .fobj (δ i)))
  fwd-mor .idxf .func = Fw
  fwd-mor .idxf .func-resp-≈ {w} {w'} = c≈fwd P E₀ {w} {w'}
  fwd-mor .famf .transf w = ci w .fwd
  fwd-mor .famf .natural {w} {w'} q = fib-cmp-nat P E₀ {w} {w'} q

  bwd-mor : F𝒟.Mor (Fib𝒟.μ-fam (P̂ P) (λ i → FamF .fobj (δ i))) (FamF .fobj (Fib𝒞.μ-fam P δ))
  bwd-mor .idxf .func = Bw
  bwd-mor .idxf .func-resp-≈ {s} {s'} = c≈bwd P E₀ {s} {s'}
  bwd-mor .famf .transf s =
    ci (Bw s) .bwd ∘
    Fibre𝒟.fib-subst (P̂ P) (E₀ .d₂) {x = s} {y = Fw (Bw s)}
      (W-≈-sym {x = Fw (Bw s)} {y = s} (cmp-bf P E₀ s))
  bwd-mor .famf .natural {s₁} {s₂} q =
    ≈-trans (tail-cong (≈-sym (Fibre𝒟.fib-trans* (P̂ P) (E₀ .d₂)
                                          {x = s₁} {y = s₂} {z = Fw (Bw s₂)} _ q)))
      (≈-sym
        (≈-trans (head-cong (iso-flip (ci (Bw s₁)) (ci (Bw s₂))
              (fib-cmp-nat P E₀ {Bw s₁} {Bw s₂}
                (c≈bwd P E₀ {s₁} {s₂} q))))
                 (tail-cong (≈-sym (Fibre𝒟.fib-trans* (P̂ P) (E₀ .d₂)
                                             {x = s₁} {y = Fw (Bw s₁)} {z = Fw (Bw s₂)} _ _)))))

  fb-≃ : F𝒟-cat._≈_ (F𝒟-cat._∘_ fwd-mor bwd-mor) (F𝒟-cat.id _)
  fb-≃ .idxf-eq = mk-≃m (λ s → cmp-bf P E₀ s)
  fb-≃ .famf-eq .transf-eq {s} =
    ≈-trans (∘-cong₂ id-left)
      (≈-trans (∘-cong₂ (head-cancel (ci (Bw s) .fwd∘bwd≈id)))
        (≈-trans (≈-sym (Fibre𝒟.fib-trans* (P̂ P) (E₀ .d₂)
                                  {x = s} {y = Fw (Bw s)} {z = s} _ _))
          (Fibre𝒟.fib-refl* (P̂ P) (E₀ .d₂) s)))

  bf-≃ : F𝒟-cat._≈_ (F𝒟-cat._∘_ bwd-mor fwd-mor) (F𝒟-cat.id _)
  bf-≃ .idxf-eq = mk-≃m (λ w → cmp-fb P E₀ w)
  bf-≃ .famf-eq .transf-eq {w} =
    ≈-trans (∘-cong₂ id-left)
      (≈-trans (∘-cong₂ (≈-trans (tail-cong (≈-sym (fib-cmp-nat P E₀ {w} {Bw (Fw w)}
                                                      (W-≈-sym {x = Bw (Fw w)} {y = w} (cmp-fb P E₀ w)))))
                                 (head-cancel (ci (Bw (Fw w)) .bwd∘fwd≈id))))
        (≈-trans (≈-sym ((FamF .fobj (Fib𝒞.μ-fam P δ)) .fam .trans*
                                  {x = w} {y = Bw (Fw w)} {z = w} _ _))
          ((FamF .fobj (Fib𝒞.μ-fam P δ)) .fam .refl* {x = w})))

  fibrewise-μ-iso : Category.Iso F𝒟.cat
                  (FamF .fobj (Fib𝒞.μ-fam P δ)) (Fib𝒟.μ-fam (P̂ P) (λ i → FamF .fobj (δ i)))
  fibrewise-μ-iso .Category.Iso.fwd = fwd-mor
  fibrewise-μ-iso .Category.Iso.bwd = bwd-mor
  fibrewise-μ-iso .Category.Iso.fwd∘bwd≈id = fb-≃
  fibrewise-μ-iso .Category.Iso.bwd∘fwd≈id = bf-≃
