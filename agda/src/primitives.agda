{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (Level; 0ℓ; suc; _⊔_; lift)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _+_)
import Data.Product as Product
import Data.Sum as Sum
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using (⊤)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts)
import prop
open import prop-setoid using (Setoid; ⊗-setoid; +-setoid; 𝟙; ⊤-isEquivalence; _∘S_)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
import matrix
import two
import fam

-- The primitives of a signature, as assumed by the operational semantics: for each sort a setoid
-- of constants and a width, and for each operation a function on constants together with a dependency
-- relation at each tuple of constants.
module primitives where

-- The setoid of tuples of constants.
sort-vals-setoid : ∀ {ℓ} {sort : Set ℓ} (sort-index : sort → Setoid 0ℓ 0ℓ) → List sort → Setoid 0ℓ 0ℓ
sort-vals-setoid si [] .Setoid.Carrier = ⊤
sort-vals-setoid si [] .Setoid._≈_ _ _ = prop.⊤
sort-vals-setoid si [] .Setoid.isEquivalence = ⊤-isEquivalence
sort-vals-setoid si (σ ∷ σs) = ⊗-setoid (si σ) (sort-vals-setoid si σs)

sorts-width : ∀ {ℓ} {A : Set ℓ} → (A → ℕ) → List A → ℕ
sorts-width w []       = 0
sorts-width w (s ∷ ss) = w s + sorts-width w ss

private
  module M𝟚 = matrix.Mat two.semiring

record Primitives {ℓ} (Sig : Signature ℓ) : Set (ℓ ⊔ suc 0ℓ) where
  open Signature Sig
  field
    sort-index : sort → Setoid 0ℓ 0ℓ
    sort-width : sort → ℕ

  sort-val : sort → Set
  sort-val s = Setoid.Carrier (sort-index s)

  sort-vals : List sort → Set
  sort-vals is = Setoid.Carrier (sort-vals-setoid sort-index is)

  bases-width : List sort → ℕ
  bases-width = sorts-width sort-width

  field
    op-fun   : ∀ {is o} → op is o →
               prop-setoid._⇒_ (sort-vals-setoid sort-index is) (sort-index o)
    op-rel   : ∀ {is o'} → op is o' →
               prop-setoid._⇒_ (sort-vals-setoid sort-index is)
                 (Category.hom-setoid M𝟚.cat (bases-width is) (sort-width o'))
    rel-pred : ∀ {is} → rel is →
               prop-setoid._⇒_ (sort-vals-setoid sort-index is) (+-setoid (𝟙 {0ℓ} {0ℓ}) 𝟙)

-- The index algebra of a family model: a sort's constants are the index elements of its interpretation,
-- and an operation acts as the index part of its interpreting morphism. Rebuilds the Fam structure by the
-- same constructions as ho-model.Interpretation, so that instantiating with a host's arguments makes its
-- models fit definitionally. Widths and dependency relations are not determined by an arbitrary model, so
-- they are supplied.
module IndexAlgebra
  {o : Level}
  (𝒞 : Category o 0ℓ 0ℓ)
  (𝒞-terminal : HasTerminal 𝒞)
  (𝒞-products : HasProducts 𝒞)
  {ℓ} (Sig : Signature ℓ)
  where

  module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞

  Fam⟨𝒞⟩-terminal = Fam⟨𝒞⟩.terminal 𝒞-terminal
  Fam⟨𝒞⟩-products = Fam⟨𝒞⟩.products.products 𝒞-products
  Fam⟨𝒞⟩-bool =
    Fam⟨𝒞⟩.coproducts .HasCoproducts.coprod
      (Fam⟨𝒞⟩-terminal .HasTerminal.witness)
      (Fam⟨𝒞⟩-terminal .HasTerminal.witness)

  PF : PointedFPCat _ _ _
  PF = PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ]

  module _ (Impl : Model PF Sig) where
    open Signature Sig
    private
      module Impl = Model Impl
      open prop-setoid._⇒_ using (func; func-resp-≈)

    index-setoid : sort → Setoid 0ℓ 0ℓ
    index-setoid s = Fam⟨𝒞⟩.Obj.idx (Impl.⟦sort⟧ s)

    index-val : sort → Set
    index-val s = Setoid.Carrier (index-setoid s)

    -- The index of a tuple of values in the product interpreting an operation's argument sorts.
    tuple : ∀ is → prop-setoid._⇒_ (sort-vals-setoid index-setoid is)
                     (Fam⟨𝒞⟩.Obj.idx (PointedFPCat.list→product PF Impl.⟦sort⟧ is))
    tuple []       .func _ = lift tt
    tuple (s ∷ ss) .func (v Product., vs) = v Product., tuple ss .func vs
    tuple []       .func-resp-≈ _ = prop.tt
    tuple (s ∷ ss) .func-resp-≈ e = prop.proj₁ e prop., tuple ss .func-resp-≈ (prop.proj₂ e)

    index-algebra : (sort-width : sort → ℕ)
                    (op-rel : ∀ {is o'} → op is o' →
                       prop-setoid._⇒_ (sort-vals-setoid index-setoid is)
                         (Category.hom-setoid M𝟚.cat (sorts-width sort-width is) (sort-width o'))) →
                    Primitives Sig
    index-algebra w r .Primitives.sort-index = index-setoid
    index-algebra w r .Primitives.sort-width = w
    index-algebra w r .Primitives.op-fun {is} ω = Fam⟨𝒞⟩.Mor.idxf (Impl.⟦op⟧ ω) ∘S tuple is
    index-algebra w r .Primitives.op-rel = r
    index-algebra w r .Primitives.rel-pred {is} ω = Fam⟨𝒞⟩.Mor.idxf (Impl.⟦rel⟧ ω) ∘S tuple is
