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
    (let module 𝒞 = Category 𝒞) (let module 𝒟 = Category 𝒟)
    (F-L : ∀ X → 𝒟.Iso (Functor.fobj F (L𝒞.L X)) (L𝒟.L (Functor.fobj F X)))
    (F-L-natural : ∀ {X Y} (f : X 𝒞.⇒ Y) →
       (F-L Y .𝒟.Iso.fwd 𝒟.∘ Functor.fmor F (L𝒞.Lmap f))
         𝒟.≈ (L𝒟.Lmap (Functor.fmor F f) 𝒟.∘ F-L X .𝒟.Iso.fwd))
    where

private
  module F𝒞 = fam.CategoryOfFamilies os (os ⊔ es) 𝒞
  module F𝒟 = fam.CategoryOfFamilies os (os ⊔ es) 𝒟
  module F𝒟C = Category F𝒟.cat
  module Srt = fam-mu-lifting.sort os es
  module Fib𝒞 = fam-mu-lifting.fibre os es CM𝒞 BP𝒞 𝟙𝒞
  module Fib𝒟 = fam-mu-lifting.fibre os es CM𝒟 BP𝒟 𝟙𝒟
  module 𝒟Pm = HasProducts (biproducts→products CM𝒟 BP𝒟)

open Srt using (Sort; mkSort)
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
  module T = Srt.Tree (λ i → δ i .idx)
  module C = Fib𝒞.Fibre δ
  module D = Fib𝒟.Fibre (λ i → FamF .fobj (δ i))

  P̂ : ∀ {j} → Fib𝒞.Poly-C j → Fib𝒟.Poly-C j
  P̂ = Poly-map FamF

  mutual
    record RelAssign (j : ℕ) : Set ℓk where
      inductive
      field
        ρ₁  : Fin j → Fin N ⊎ Sort N
        ρ₂  : Fin j → Fin N ⊎ Sort N
        d₁  : ∀ i → C.DecoAssign (ρ₁ i)
        d₂  : ∀ i → D.DecoAssign (ρ₂ i)
        rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)

    data SRel : (r₁ r₂ : Fin N ⊎ Sort N) → C.DecoAssign r₁ → D.DecoAssign r₂ → Set ℓk where
      env : ∀ {p} → SRel (inj₁ p) (inj₁ p) (lift tt) (lift tt)
      srt : ∀ {s₁ s₂ e₁ e₂} → SortRel s₁ s₂ e₁ e₂ → SRel (inj₂ s₁) (inj₂ s₂) e₁ e₂

    data SortRel : (s₁ s₂ : Sort N) → C.Deco s₁ → D.Deco s₂ → Set ℓk where
      mk : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
           SortRel (mkSort Fib𝒞.∣ Q ∣ (E .RelAssign.ρ₁)) (mkSort Fib𝒟.∣ P̂ Q ∣ (E .RelAssign.ρ₂))
                   (C.mkDeco Q (E .RelAssign.d₁)) (D.mkDeco (P̂ Q) (E .RelAssign.d₂))

  open RelAssign public

  ext : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) → RelAssign j → RelAssign (sucℕ j)
  ext Q E .ρ₁ = extend (E .ρ₁) (inj₂ (mkSort Fib𝒞.∣ Q ∣ (E .ρ₁)))
  ext Q E .ρ₂ = extend (E .ρ₂) (inj₂ (mkSort Fib𝒟.∣ P̂ Q ∣ (E .ρ₂)))
  ext Q E .d₁ = C.deco-ext Q (E .d₁)
  ext Q E .d₂ = D.deco-ext (P̂ Q) (E .d₂)
  ext Q E .rel Fin.zero    = srt (mk Q E)
  ext Q E .rel (Fin.suc i) = E .rel i

  mutual
    cfwd : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
           T.W Fib𝒞.∣ Q ∣ (E .ρ₁) → T.W Fib𝒟.∣ P̂ Q ∣ (E .ρ₂)
    cfwd Q E (T.sup x) = T.sup (shape-cfwd Q (ext Q E) x)

    shape-cfwd : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j) →
                 T.⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁) → T.⟦ Fib𝒟.∣ P̂ Q ∣ ⟧shape (E .ρ₂)
    shape-cfwd (Poly.const A) E x = x
    shape-cfwd (Poly.var i)   E x = el-cfwd (E .rel i) x
    shape-cfwd (Q Poly.+ R) E (inj₁ x) = inj₁ (shape-cfwd Q E x)
    shape-cfwd (Q Poly.+ R) E (inj₂ y) = inj₂ (shape-cfwd R E y)
    shape-cfwd (Q Poly.× R) E (x , y) = shape-cfwd Q E x , shape-cfwd R E y
    shape-cfwd (Poly.μ Q')  E t = cfwd Q' E t

    el-cfwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → T.El r₁ → T.El r₂
    el-cfwd env x = x
    el-cfwd (srt (mk Q E)) x = cfwd Q E x

  mutual
    c≈fwd : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
            {x y : T.W Fib𝒞.∣ Q ∣ (E .ρ₁)} → T.W-≈ x y →
            T.W-≈ (cfwd Q E x) (cfwd Q E y)
    c≈fwd Q E {T.sup x} {T.sup y} p = shape≈-cfwd Q (ext Q E) p

    shape≈-cfwd : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j) →
                  {x y : T.⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)} → T.shape≈ Fib𝒞.∣ Q ∣ (E .ρ₁) x y →
                  T.shape≈ Fib𝒟.∣ P̂ Q ∣ (E .ρ₂) (shape-cfwd Q E x) (shape-cfwd Q E y)
    shape≈-cfwd (Poly.const A) E p = p
    shape≈-cfwd (Poly.var i)   E p = elEq-cfwd (E .rel i) p
    shape≈-cfwd (Q Poly.+ R) E {inj₁ _} {inj₁ _} p = shape≈-cfwd Q E p
    shape≈-cfwd (Q Poly.+ R) E {inj₂ _} {inj₂ _} p = shape≈-cfwd R E p
    shape≈-cfwd (Q Poly.× R) E {_ , _} {_ , _} (p ,ₚ q) = shape≈-cfwd Q E p ,ₚ shape≈-cfwd R E q
    shape≈-cfwd (Poly.μ Q')  E {x} {y} p = c≈fwd Q' E {x} {y} p

    elEq-cfwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : T.El r₁} →
                T.elEq r₁ x y → T.elEq r₂ (el-cfwd r x) (el-cfwd r y)
    elEq-cfwd env p = p
    elEq-cfwd (srt (mk Q E)) {x} {y} p = c≈fwd Q E {x} {y} p

  mutual
    cbwd : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
           T.W Fib𝒟.∣ P̂ Q ∣ (E .ρ₂) → T.W Fib𝒞.∣ Q ∣ (E .ρ₁)
    cbwd Q E (T.sup x) = T.sup (shape-cbwd Q (ext Q E) x)

    shape-cbwd : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j) →
                 T.⟦ Fib𝒟.∣ P̂ Q ∣ ⟧shape (E .ρ₂) → T.⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)
    shape-cbwd (Poly.const A) E x = x
    shape-cbwd (Poly.var i)   E x = el-cbwd (E .rel i) x
    shape-cbwd (Q Poly.+ R) E (inj₁ x) = inj₁ (shape-cbwd Q E x)
    shape-cbwd (Q Poly.+ R) E (inj₂ y) = inj₂ (shape-cbwd R E y)
    shape-cbwd (Q Poly.× R) E (x , y) = shape-cbwd Q E x , shape-cbwd R E y
    shape-cbwd (Poly.μ Q')  E t = cbwd Q' E t

    el-cbwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → T.El r₂ → T.El r₁
    el-cbwd env x = x
    el-cbwd (srt (mk Q E)) x = cbwd Q E x

  mutual
    c≈bwd : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j) →
            {x y : T.W Fib𝒟.∣ P̂ Q ∣ (E .ρ₂)} → T.W-≈ x y →
            T.W-≈ (cbwd Q E x) (cbwd Q E y)
    c≈bwd Q E {T.sup x} {T.sup y} p = shape≈-cbwd Q (ext Q E) p

    shape≈-cbwd : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j) →
                  {x y : T.⟦ Fib𝒟.∣ P̂ Q ∣ ⟧shape (E .ρ₂)} → T.shape≈ Fib𝒟.∣ P̂ Q ∣ (E .ρ₂) x y →
                  T.shape≈ Fib𝒞.∣ Q ∣ (E .ρ₁) (shape-cbwd Q E x) (shape-cbwd Q E y)
    shape≈-cbwd (Poly.const A) E p = p
    shape≈-cbwd (Poly.var i)   E p = elEq-cbwd (E .rel i) p
    shape≈-cbwd (Q Poly.+ R) E {inj₁ _} {inj₁ _} p = shape≈-cbwd Q E p
    shape≈-cbwd (Q Poly.+ R) E {inj₂ _} {inj₂ _} p = shape≈-cbwd R E p
    shape≈-cbwd (Q Poly.× R) E {_ , _} {_ , _} (p ,ₚ q) = shape≈-cbwd Q E p ,ₚ shape≈-cbwd R E q
    shape≈-cbwd (Poly.μ Q')  E {x} {y} p = c≈bwd Q' E {x} {y} p

    elEq-cbwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : T.El r₂} →
                T.elEq r₂ x y → T.elEq r₁ (el-cbwd r x) (el-cbwd r y)
    elEq-cbwd env p = p
    elEq-cbwd (srt (mk Q E)) {x} {y} p = c≈bwd Q E {x} {y} p

  mutual
    c-fb : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j)
           (x : T.W Fib𝒞.∣ Q ∣ (E .ρ₁)) →
           T.W-≈ (cbwd Q E (cfwd Q E x)) x
    c-fb Q E (T.sup x) = shape-cfb Q (ext Q E) x

    shape-cfb : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j)
                (x : T.⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)) →
                T.shape≈ Fib𝒞.∣ Q ∣ (E .ρ₁) (shape-cbwd Q E (shape-cfwd Q E x)) x
    shape-cfb (Poly.const A) E x = IsEquivalence.refl (Setoid.isEquivalence (A .idx))
    shape-cfb (Poly.var i)   E x = el-cfb (E .rel i) x
    shape-cfb (Q Poly.+ R) E (inj₁ x) = shape-cfb Q E x
    shape-cfb (Q Poly.+ R) E (inj₂ y) = shape-cfb R E y
    shape-cfb (Q Poly.× R) E (x , y) = shape-cfb Q E x ,ₚ shape-cfb R E y
    shape-cfb (Poly.μ Q')  E t = c-fb Q' E t

    el-cfb : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : T.El r₁) → T.elEq r₁ (el-cbwd r (el-cfwd r x)) x
    el-cfb (env {p}) x = T.elEq-refl (inj₁ p) x
    el-cfb (srt (mk Q E)) x = c-fb Q E x

  mutual
    c-bf : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j)
           (y : T.W Fib𝒟.∣ P̂ Q ∣ (E .ρ₂)) →
           T.W-≈ (cfwd Q E (cbwd Q E y)) y
    c-bf Q E (T.sup y) = shape-cbf Q (ext Q E) y

    shape-cbf : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j)
                (y : T.⟦ Fib𝒟.∣ P̂ Q ∣ ⟧shape (E .ρ₂)) →
                T.shape≈ Fib𝒟.∣ P̂ Q ∣ (E .ρ₂) (shape-cfwd Q E (shape-cbwd Q E y)) y
    shape-cbf (Poly.const A) E y = IsEquivalence.refl (Setoid.isEquivalence (A .idx))
    shape-cbf (Poly.var i)   E y = el-cbf (E .rel i) y
    shape-cbf (Q Poly.+ R) E (inj₁ y) = shape-cbf Q E y
    shape-cbf (Q Poly.+ R) E (inj₂ y) = shape-cbf R E y
    shape-cbf (Q Poly.× R) E (x , y) = shape-cbf Q E x ,ₚ shape-cbf R E y
    shape-cbf (Poly.μ Q')  E t = c-bf Q' E t

    el-cbf : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (y : T.El r₂) → T.elEq r₂ (el-cfwd r (el-cbwd r y)) y
    el-cbf (env {p}) y = T.elEq-refl (inj₁ p) y
    el-cbf (srt (mk Q E)) y = c-bf Q E y

  mutual
    fib-ciso : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j)
               (w : T.W Fib𝒞.∣ Q ∣ (E .ρ₁)) →
               𝒟.Iso (F .fobj (C.fib Q (E .d₁) w)) (D.fib (P̂ Q) (E .d₂) (cfwd Q E w))
    fib-ciso Q E (T.sup x) = fib-shape-ciso Q (ext Q E) x

    fib-shape-ciso : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j)
                     (x : T.⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)) →
                     𝒟.Iso (F .fobj (C.fib-shape Q (E .d₁) x))
                            (D.fib-shape (P̂ Q) (E .d₂) (shape-cfwd Q E x))
    fib-shape-ciso (Poly.const A) E x = Iso-refl
    fib-shape-ciso (Poly.var i)   E x = fib-el-ciso (E .rel i) x
    fib-shape-ciso (Q Poly.+ R) E (inj₁ x) = Iso-trans (F-L _) (L-iso (fib-shape-ciso Q E x))
    fib-shape-ciso (Q Poly.+ R) E (inj₂ y) = Iso-trans (F-L _) (L-iso (fib-shape-ciso R E y))
    fib-shape-ciso (Q Poly.× R) E (x , y) =
      Iso-trans (F-L _)
        (L-iso (Iso-trans (IsIso→Iso F-prod)
                 (𝒟Pm.product-preserves-iso
                   (fib-shape-ciso Q E x)
                   (fib-shape-ciso R E y))))
    fib-shape-ciso (Poly.μ Q')  E t = fib-ciso Q' E t

    fib-el-ciso : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : T.El r₁) →
                  𝒟.Iso (F .fobj (C.fib-el r₁ e₁ x)) (D.fib-el r₂ e₂ (el-cfwd r x))
    fib-el-ciso (env {p}) x = Iso-refl
    fib-el-ciso (srt (mk Q E)) x = fib-ciso Q E x

  open preserve-chosen-products-consequences F (biproducts→products CM𝒞 BP𝒞) (biproducts→products CM𝒟 BP𝒟) F-prod
    using (mul⁻¹-natural)

  mutual
    fib-cnat : ∀ {j} (Q : Fib𝒞.Poly-C (sucℕ j)) (E : RelAssign j)
               {w w' : T.W Fib𝒞.∣ Q ∣ (E .ρ₁)} (p : T.W-≈ w w') →
               ((fib-ciso Q E w' .fwd)
                 ∘ F .fmor (C.fib-subst Q (E .d₁) {x = w} {y = w'} p))
               ≈ ((D.fib-subst (P̂ Q) (E .d₂)
                        {x = cfwd Q E w} {y = cfwd Q E w'}
                        (c≈fwd Q E {w} {w'} p))
                     ∘ (fib-ciso Q E w .fwd))
    fib-cnat Q E {T.sup x} {T.sup x'} p = fib-shape-cnat Q (ext Q E) {x} {x'} p

    fib-shape-cnat : ∀ {j} (Q : Fib𝒞.Poly-C j) (E : RelAssign j)
                     {x x' : T.⟦ Fib𝒞.∣ Q ∣ ⟧shape (E .ρ₁)} (p : T.shape≈ Fib𝒞.∣ Q ∣ (E .ρ₁) x x') →
                     ((fib-shape-ciso Q E x' .fwd)
                       ∘ F .fmor (C.fib-shape-subst Q (E .d₁) p))
                     ≈ ((D.fib-shape-subst (P̂ Q) (E .d₂) (shape≈-cfwd Q E {x} {x'} p))
                           ∘ (fib-shape-ciso Q E x .fwd))
    fib-shape-cnat (Poly.const A) E p = ≈-trans id-left (≈-sym id-right)
    fib-shape-cnat (Poly.var i)   E p = fib-el-cnat (E .rel i) p
    fib-shape-cnat (Q Poly.+ R) E {inj₁ x} {inj₁ x'} p =
      root-step (fib-shape-ciso Q E x') (fib-shape-ciso Q E x)
        (fib-shape-cnat Q E p)
    fib-shape-cnat (Q Poly.+ R) E {inj₂ y} {inj₂ y'} p =
      root-step (fib-shape-ciso R E y') (fib-shape-ciso R E y)
        (fib-shape-cnat R E p)
    fib-shape-cnat (Q Poly.× R) E {x₁ , x₂} {x₁' , x₂'} (p₁ ,ₚ p₂) =
      root-step pI' pI
        (≈-trans (tail-cong (mul⁻¹-natural {f = s₁} {g = s₂}))
         (head-cong-assoc (≈-trans (≈-sym (𝒟Pm.prod-m-comp _ _ _ _))
                            (≈-trans
                              (𝒟Pm.prod-m-cong
                                (fib-shape-cnat Q E {x₁} {x₁'} p₁)
                                (fib-shape-cnat R E {x₂} {x₂'} p₂))
                              (𝒟Pm.prod-m-comp _ _ _ _)))))
      where
        s₁ = C.fib-shape-subst Q (E .d₁) p₁
        s₂ = C.fib-shape-subst R (E .d₁) p₂

        pI : 𝒟.Iso _ _
        pI = Iso-trans (IsIso→Iso F-prod)
               (𝒟Pm.product-preserves-iso
                 (fib-shape-ciso Q E x₁)
                 (fib-shape-ciso R E x₂))

        pI' : 𝒟.Iso _ _
        pI' = Iso-trans (IsIso→Iso F-prod)
                (𝒟Pm.product-preserves-iso
                  (fib-shape-ciso Q E x₁')
                  (fib-shape-ciso R E x₂'))
    fib-shape-cnat (Poly.μ Q')  E {t} {t'} p = fib-cnat Q' E {t} {t'} p

    fib-el-cnat : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x x' : T.El r₁} (p : T.elEq r₁ x x') →
                  ((fib-el-ciso r x' .fwd)
                    ∘ F .fmor (C.fib-el-subst r₁ e₁ p))
                  ≈ ((D.fib-el-subst r₂ e₂ (elEq-cfwd r {x} {x'} p))
                        ∘ (fib-el-ciso r x .fwd))
    fib-el-cnat (env {p}) q = ≈-trans id-left (≈-sym id-right)
    fib-el-cnat (srt (mk Q E)) {x} {x'} q = fib-cnat Q E {x} {x'} q

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

    Fw = cfwd P E₀
    Bw = cbwd P E₀
    ci = fib-ciso P E₀

  fwd-mor : F𝒟.Mor (FamF .fobj (Fib𝒞.μ-fam P δ)) (Fib𝒟.μ-fam (P̂ P) (λ i → FamF .fobj (δ i)))
  fwd-mor .idxf .func = Fw
  fwd-mor .idxf .func-resp-≈ {w} {w'} = c≈fwd P E₀ {w} {w'}
  fwd-mor .famf .transf w = ci w .fwd
  fwd-mor .famf .natural {w} {w'} q = fib-cnat P E₀ {w} {w'} q

  bwd-mor : F𝒟.Mor (Fib𝒟.μ-fam (P̂ P) (λ i → FamF .fobj (δ i))) (FamF .fobj (Fib𝒞.μ-fam P δ))
  bwd-mor .idxf .func = Bw
  bwd-mor .idxf .func-resp-≈ {s} {s'} = c≈bwd P E₀ {s} {s'}
  bwd-mor .famf .transf s =
    ci (Bw s) .bwd ∘
    D.fib-subst (P̂ P) (E₀ .d₂) {x = s} {y = Fw (Bw s)}
      (T.W-≈-sym {x = Fw (Bw s)} {y = s} (c-bf P E₀ s))
  bwd-mor .famf .natural {s₁} {s₂} q =
    ≈-trans (tail-cong (≈-sym (D.fib-trans* (P̂ P) (E₀ .d₂)
                                          {x = s₁} {y = s₂} {z = Fw (Bw s₂)} _ q)))
      (≈-sym
        (≈-trans (head-cong (iso-flip (ci (Bw s₁)) (ci (Bw s₂))
              (fib-cnat P E₀ {Bw s₁} {Bw s₂}
                (c≈bwd P E₀ {s₁} {s₂} q))))
                 (tail-cong (≈-sym (D.fib-trans* (P̂ P) (E₀ .d₂)
                                             {x = s₁} {y = Fw (Bw s₁)} {z = Fw (Bw s₂)} _ _)))))

  fb-≃ : F𝒟C._≈_ (F𝒟C._∘_ fwd-mor bwd-mor) (F𝒟C.id _)
  fb-≃ .idxf-eq = mk-≃m (λ s → c-bf P E₀ s)
  fb-≃ .famf-eq .transf-eq {s} =
    ≈-trans (∘-cong₂ id-left)
      (≈-trans (∘-cong₂ (head-cancel (ci (Bw s) .fwd∘bwd≈id)))
        (≈-trans (≈-sym (D.fib-trans* (P̂ P) (E₀ .d₂)
                                  {x = s} {y = Fw (Bw s)} {z = s} _ _))
          (D.fib-refl* (P̂ P) (E₀ .d₂) s)))

  bf-≃ : F𝒟C._≈_ (F𝒟C._∘_ bwd-mor fwd-mor) (F𝒟C.id _)
  bf-≃ .idxf-eq = mk-≃m (λ w → c-fb P E₀ w)
  bf-≃ .famf-eq .transf-eq {w} =
    ≈-trans (∘-cong₂ id-left)
      (≈-trans (∘-cong₂ (≈-trans (tail-cong (≈-sym (fib-cnat P E₀ {w} {Bw (Fw w)}
                                                      (T.W-≈-sym {x = Bw (Fw w)} {y = w} (c-fb P E₀ w)))))
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
