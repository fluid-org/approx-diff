{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (Level; 0ℓ; suc; _⊔_; lift)
open import Data.List using (List; []; _∷_)
import Data.Product as Product
import Data.Sum as Sum
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using (⊤)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts)
open import prop-setoid using (Setoid)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
import fam

-- Value-level interpretation of a signature, as used by the operational semantics.
module language-operational.algebra where

sort-vals : ∀ {ℓ ℓ'} {sort : Set ℓ} (sort-val : sort → Set ℓ') → List sort → Set ℓ'
sort-vals sv []       = ⊤
sort-vals sv (σ ∷ σs) = sv σ Product.× sort-vals sv σs

record Algebra {ℓ} (Sig : Signature ℓ) ℓ' : Set (ℓ ⊔ suc ℓ') where
  open Signature Sig
  field
    sort-val : sort → Set ℓ'
    op-fun   : ∀ {is o} → op is o → sort-vals sort-val is → sort-val o
    rel-pred : ∀ {is}   → rel is  → sort-vals sort-val is → ⊤ {ℓ'} Sum.⊎ ⊤ {ℓ'}

-- The index algebra of a family model: a sort's values are the index elements of its interpretation, and an
-- operation acts as the index part of its interpreting morphism. Rebuilds the Fam structure by the same
-- constructions as ho-model.Interpretation, so that instantiating with a host's arguments makes its models
-- fit definitionally.
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
      open prop-setoid._⇒_ using (func)

    index-val : sort → Set
    index-val s = Setoid.Carrier (Fam⟨𝒞⟩.Obj.idx (Impl.⟦sort⟧ s))

    private
      tuple : ∀ is → sort-vals index-val is →
              Setoid.Carrier (Fam⟨𝒞⟩.Obj.idx (PointedFPCat.list→product PF Impl.⟦sort⟧ is))
      tuple []       _                  = lift tt
      tuple (s ∷ ss) (v Product., vs) = v Product., tuple ss vs

    index-algebra : Algebra Sig 0ℓ
    index-algebra .Algebra.sort-val = index-val
    index-algebra .Algebra.op-fun ω vs = func (Fam⟨𝒞⟩.Mor.idxf (Impl.⟦op⟧ ω)) (tuple _ vs)
    index-algebra .Algebra.rel-pred ω vs
      with func (Fam⟨𝒞⟩.Mor.idxf (Impl.⟦rel⟧ ω)) (tuple _ vs)
    ... | Sum.inj₁ _ = Sum.inj₁ (lift tt)
    ... | Sum.inj₂ _ = Sum.inj₂ (lift tt)
