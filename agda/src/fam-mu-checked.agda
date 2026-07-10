{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Checking commutes with μ at constant-free skeletons. A family is "checked"
-- by applying a functor G to its singleton fibres; the μ-carrier of a skeleton
-- over an environment then agrees with the μ-carrier of the same skeleton over
-- the checked environment. The two skeletons live over the two Fam categories
-- but share their sorts and trees, which are built from index setoids alone;
-- the transports below relate the two erasures by recursion on the polynomial,
-- with identities at the leaves.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ) renaming (suc to sucℕ; _+_ to _+ℕ_)
import Data.Fin as Fin
open Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using () renaming (_,_ to _,ₚ_)
open import categories using (Category; HasTerminal; HasProducts)
open import functor using (Functor; _∘F_)
open import finite-product-functor using (preserve-chosen-products)
open import prop-setoid using (Setoid)
open import indexed-family using (functor→fam)
import fam
import fam-presentation
import polynomial-functor-2
import fam-mu-types-2.shape
import fam-mu-types-2.fibre

module fam-mu-checked {o m e o₂ m₂ e₂} (os es : Level)
    {𝒞 : Category o m e} (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞)
    {𝒢 : Category o₂ m₂ e₂} (𝒢T : HasTerminal 𝒢) (𝒢P : HasProducts 𝒢)
    (G : Functor (fam.CategoryOfFamilies.cat os (os ⊔ es) 𝒞) 𝒢)
    (G-prod : preserve-chosen-products G
                (fam.CategoryOfFamilies.products.products os (os ⊔ es) 𝒞 𝒞P) 𝒢P)
    where

private
  module F𝒞 = fam.CategoryOfFamilies os (os ⊔ es) 𝒞
  module F𝒢 = fam.CategoryOfFamilies os (os ⊔ es) 𝒢
  module Sh = fam-mu-types-2.shape os es
  module Fc = fam-mu-types-2.fibre os es 𝒞T 𝒞P
  module Fg = fam-mu-types-2.fibre os es 𝒢T 𝒢P
  module PresC = fam-presentation os (os ⊔ es) {𝒞}

open Sh using (Sort; mkSort)
open polynomial-functor-2 using (Poly; #c; skeleton-go; extend)
open F𝒞.Obj

ℓk : Level
ℓk = o ⊔ m ⊔ e ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ lsuc os ⊔ lsuc es

-- The checked family: G applied to the singleton fibres, over the same index
-- setoid.
check : F𝒞.Obj → F𝒢.Obj
check X .F𝒢.Obj.idx = X .idx
check X .F𝒢.Obj.fam = functor→fam (G ∘F PresC.singletons X)

module Checked {N : ℕ} (k : ℕ) (δ : Fin N → F𝒞.Obj) where
  module T  = Sh.Tree (λ i → δ i .idx)
  module C  = Fc.Fibre δ
  module Gd = Fg.Fibre (λ i → check (δ i))

  -- The same polynomial skeletonised into either Fam category.
  skC : ∀ {j} (Q : Poly F𝒞.cat j) → (Fin (#c Q) → Fin k) → Poly F𝒞.cat (j +ℕ k)
  skC = skeleton-go

  skG : ∀ {j} (Q : Poly F𝒞.cat j) → (Fin (#c Q) → Fin k) → Poly F𝒢.cat (j +ℕ k)
  skG = skeleton-go

  -- Relate references and decorated sorts of the two skeletons: environment
  -- positions coincide, and sorts relate recursively through the μ-body they
  -- both skeletonise.
  mutual
    data SRel : (r₁ r₂ : Fin N ⊎ Sort N) → C.DecoRes r₁ → Gd.DecoRes r₂ → Set ℓk where
      env : ∀ {p} → SRel (inj₁ p) (inj₁ p) (lift tt) (lift tt)
      srt : ∀ {s₁ s₂ e₁ e₂} → SortChk s₁ s₂ e₁ e₂ → SRel (inj₂ s₁) (inj₂ s₂) e₁ e₂

    data SortChk : (s₁ s₂ : Sort N) → C.Deco s₁ → Gd.Deco s₂ → Set ℓk where
      mk : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoRes (ρ₁ i)) (d₂ : ∀ i → Gd.DecoRes (ρ₂ i)) →
           (∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           SortChk (mkSort Fc.∣ skC Q ι ∣ ρ₁) (mkSort Fg.∣ skG Q ι ∣ ρ₂)
                   (C.mkDeco (skC Q ι) d₁) (Gd.mkDeco (skG Q ι) d₂)

  -- Forward tree transport, by recursion on the polynomial; the leaves are
  -- identities.
  mutual
    cfwd : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoRes (ρ₁ i)) (d₂ : ∀ i → Gd.DecoRes (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           T.W Fc.∣ skC Q ι ∣ ρ₁ → T.W Fg.∣ skG Q ι ∣ ρ₂
    cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      T.sup (shape-cfwd Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
               (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
               (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
               (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) x)

    extend-rel : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
                 (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoRes (ρ₁ i)) (d₂ : ∀ i → Gd.DecoRes (ρ₂ i))
                 (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
                 ∀ i → SRel (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)) i)
                            (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)) i)
                            (C.deco-ext (skC Q ι) d₁ i)
                            (Gd.deco-ext (skG Q ι) d₂ i)
    extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel Fin.zero    = srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)
    extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel (Fin.suc i) = rel i

    shape-cfwd : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                 (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoRes (η₁ i)) (d₂ : ∀ i → Gd.DecoRes (η₂ i))
                 (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                 T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁ → T.⟦ Fg.∣ skG Q ι ∣ ⟧shape η₂
    shape-cfwd {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel x = el-cfwd (rel (jv ↑ʳ ι Fin.zero)) x
    shape-cfwd (Poly.var i)   ι η₁ η₂ d₁ d₂ rel x = el-cfwd (rel (i ↑ˡ k)) x
    shape-cfwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ x) =
      inj₁ (shape-cfwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x)
    shape-cfwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      inj₂ (shape-cfwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y)
    shape-cfwd (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cfwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
      , shape-cfwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cfwd (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = cfwd Q' ι η₁ η₂ d₁ d₂ rel t

    el-cfwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → T.El r₁ → T.El r₂
    el-cfwd env x = x
    el-cfwd (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) x = cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel x

  -- The forward transport preserves bisimilarity.
  mutual
    c≈fwd : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
            (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
            (d₁ : ∀ i → C.DecoRes (ρ₁ i)) (d₂ : ∀ i → Gd.DecoRes (ρ₂ i))
            (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
            {x y : T.W Fc.∣ skC Q ι ∣ ρ₁} → T.W-≈ x y →
            T.W-≈ (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel x) (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel y)
    c≈fwd Q ι ρ₁ ρ₂ d₁ d₂ rel {T.sup x} {T.sup y} p =
      shape≈-cfwd Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) p

    shape≈-cfwd : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                  (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                  (d₁ : ∀ i → C.DecoRes (η₁ i)) (d₂ : ∀ i → Gd.DecoRes (η₂ i))
                  (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                  {x y : T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁} → T.shape≈ Fc.∣ skC Q ι ∣ η₁ x y →
                  T.shape≈ Fg.∣ skG Q ι ∣ η₂ (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel x) (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel y)
    shape≈-cfwd {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel p = elEq-cfwd (rel (jv ↑ʳ ι Fin.zero)) p
    shape≈-cfwd (Poly.var i)   ι η₁ η₂ d₁ d₂ rel p = elEq-cfwd (rel (i ↑ˡ k)) p
    shape≈-cfwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₁ _} {inj₁ _} p =
      shape≈-cfwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
    shape≈-cfwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₂ _} {inj₂ _} p =
      shape≈-cfwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel p
    shape≈-cfwd (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-cfwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
      ,ₚ shape≈-cfwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel q
    shape≈-cfwd (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel {x} {y} p = c≈fwd Q' ι η₁ η₂ d₁ d₂ rel {x} {y} p

    elEq-cfwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : T.El r₁} →
                T.elEq r₁ x y → T.elEq r₂ (el-cfwd r x) (el-cfwd r y)
    elEq-cfwd env p = p
    elEq-cfwd (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) {x} {y} p = c≈fwd Q ι ρ₁ ρ₂ d₁ d₂ rel {x} {y} p

  -- Backward tree transport.
  mutual
    cbwd : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoRes (ρ₁ i)) (d₂ : ∀ i → Gd.DecoRes (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           T.W Fg.∣ skG Q ι ∣ ρ₂ → T.W Fc.∣ skC Q ι ∣ ρ₁
    cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      T.sup (shape-cbwd Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
               (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
               (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
               (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) x)

    shape-cbwd : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                 (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoRes (η₁ i)) (d₂ : ∀ i → Gd.DecoRes (η₂ i))
                 (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                 T.⟦ Fg.∣ skG Q ι ∣ ⟧shape η₂ → T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁
    shape-cbwd {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel x = el-cbwd (rel (jv ↑ʳ ι Fin.zero)) x
    shape-cbwd (Poly.var i)   ι η₁ η₂ d₁ d₂ rel x = el-cbwd (rel (i ↑ˡ k)) x
    shape-cbwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ x) =
      inj₁ (shape-cbwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x)
    shape-cbwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      inj₂ (shape-cbwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y)
    shape-cbwd (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cbwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
      , shape-cbwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cbwd (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = cbwd Q' ι η₁ η₂ d₁ d₂ rel t

    el-cbwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → T.El r₂ → T.El r₁
    el-cbwd env x = x
    el-cbwd (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) x = cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel x

  -- The backward transport preserves bisimilarity.
  mutual
    c≈bwd : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
            (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
            (d₁ : ∀ i → C.DecoRes (ρ₁ i)) (d₂ : ∀ i → Gd.DecoRes (ρ₂ i))
            (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
            {x y : T.W Fg.∣ skG Q ι ∣ ρ₂} → T.W-≈ x y →
            T.W-≈ (cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel x) (cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel y)
    c≈bwd Q ι ρ₁ ρ₂ d₁ d₂ rel {T.sup x} {T.sup y} p =
      shape≈-cbwd Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) p

    shape≈-cbwd : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                  (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                  (d₁ : ∀ i → C.DecoRes (η₁ i)) (d₂ : ∀ i → Gd.DecoRes (η₂ i))
                  (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                  {x y : T.⟦ Fg.∣ skG Q ι ∣ ⟧shape η₂} → T.shape≈ Fg.∣ skG Q ι ∣ η₂ x y →
                  T.shape≈ Fc.∣ skC Q ι ∣ η₁ (shape-cbwd Q ι η₁ η₂ d₁ d₂ rel x) (shape-cbwd Q ι η₁ η₂ d₁ d₂ rel y)
    shape≈-cbwd {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel p = elEq-cbwd (rel (jv ↑ʳ ι Fin.zero)) p
    shape≈-cbwd (Poly.var i)   ι η₁ η₂ d₁ d₂ rel p = elEq-cbwd (rel (i ↑ˡ k)) p
    shape≈-cbwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₁ _} {inj₁ _} p =
      shape≈-cbwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
    shape≈-cbwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₂ _} {inj₂ _} p =
      shape≈-cbwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel p
    shape≈-cbwd (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-cbwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
      ,ₚ shape≈-cbwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel q
    shape≈-cbwd (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel {x} {y} p = c≈bwd Q' ι η₁ η₂ d₁ d₂ rel {x} {y} p

    elEq-cbwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : T.El r₂} →
                T.elEq r₂ x y → T.elEq r₁ (el-cbwd r x) (el-cbwd r y)
    elEq-cbwd env p = p
    elEq-cbwd (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) {x} {y} p = c≈bwd Q ι ρ₁ ρ₂ d₁ d₂ rel {x} {y} p

  -- Round trips: the two transports are mutually inverse up to bisimilarity.
  mutual
    c-fb : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoRes (ρ₁ i)) (d₂ : ∀ i → Gd.DecoRes (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           (x : T.W Fc.∣ skC Q ι ∣ ρ₁) →
           T.W-≈ (cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel x)) x
    c-fb Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      shape-cfb Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) x

    shape-cfb : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                (d₁ : ∀ i → C.DecoRes (η₁ i)) (d₂ : ∀ i → Gd.DecoRes (η₂ i))
                (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                (x : T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁) →
                T.shape≈ Fc.∣ skC Q ι ∣ η₁ (shape-cbwd Q ι η₁ η₂ d₁ d₂ rel (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel x)) x
    shape-cfb {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel x = el-cfb (rel (jv ↑ʳ ι Fin.zero)) x
    shape-cfb (Poly.var i)   ι η₁ η₂ d₁ d₂ rel x = el-cfb (rel (i ↑ˡ k)) x
    shape-cfb (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ x) =
      shape-cfb Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
    shape-cfb (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      shape-cfb R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cfb (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cfb Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
      ,ₚ shape-cfb R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cfb (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = c-fb Q' ι η₁ η₂ d₁ d₂ rel t

    el-cfb : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : T.El r₁) →
             T.elEq r₁ (el-cbwd r (el-cfwd r x)) x
    el-cfb (env {p}) x = T.elEq-refl (inj₁ p) x
    el-cfb (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) x = c-fb Q ι ρ₁ ρ₂ d₁ d₂ rel x

  mutual
    c-bf : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoRes (ρ₁ i)) (d₂ : ∀ i → Gd.DecoRes (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           (y : T.W Fg.∣ skG Q ι ∣ ρ₂) →
           T.W-≈ (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel (cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel y)) y
    c-bf Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup y) =
      shape-cbf Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) y

    shape-cbf : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                (d₁ : ∀ i → C.DecoRes (η₁ i)) (d₂ : ∀ i → Gd.DecoRes (η₂ i))
                (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                (y : T.⟦ Fg.∣ skG Q ι ∣ ⟧shape η₂) →
                T.shape≈ Fg.∣ skG Q ι ∣ η₂ (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel (shape-cbwd Q ι η₁ η₂ d₁ d₂ rel y)) y
    shape-cbf {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel y = el-cbf (rel (jv ↑ʳ ι Fin.zero)) y
    shape-cbf (Poly.var i)   ι η₁ η₂ d₁ d₂ rel y = el-cbf (rel (i ↑ˡ k)) y
    shape-cbf (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ y) =
      shape-cbf Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel y
    shape-cbf (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      shape-cbf R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cbf (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cbf Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
      ,ₚ shape-cbf R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cbf (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = c-bf Q' ι η₁ η₂ d₁ d₂ rel t

    el-cbf : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (y : T.El r₂) →
             T.elEq r₂ (el-cfwd r (el-cbwd r y)) y
    el-cbf (env {p}) y = T.elEq-refl (inj₁ p) y
    el-cbf (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) y = c-bf Q ι ρ₁ ρ₂ d₁ d₂ rel y
