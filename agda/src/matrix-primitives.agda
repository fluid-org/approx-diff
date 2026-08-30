{-# OPTIONS --postfix-projections --prop --safe #-}

-- The interpretation of the primitives over families of dimensions: a sort's fibre is the number
-- of scalar positions its constants carry, and an operation's fibre map at a tuple of constants is
-- its dependency relation there, presented as a matrix. The width of an argument list is the
-- biproduct of the arguments' widths, so collecting the arguments is the monoidal comparison alone.
open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import prop-setoid using (Setoid; idS; _∘S_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import categories using (Category; HasProducts; HasTerminal; HasCoproducts)
open import cmon-enriched using (biproducts→products)
import prop
open prop using (_,_)
open import signature.interpretation using (Interpretation; sort-vals-setoid)
import indexed-family
import matrix
import fam

module matrix-primitives {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module M = matrix.Mat S

M-products : HasProducts M.cat
M-products = biproducts→products M.cmon M.biproduct

module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ M.cat

Fam⟨𝒞⟩-terminal = Fam⟨𝒞⟩.terminal M.terminal
Fam⟨𝒞⟩-products = Fam⟨𝒞⟩.products.products M-products
Fam⟨𝒞⟩-coproducts = Fam⟨𝒞⟩.coproducts

Fam⟨𝒞⟩-bool =
  Fam⟨𝒞⟩-coproducts .HasCoproducts.coprod
    (Fam⟨𝒞⟩-terminal .HasTerminal.witness)
    (Fam⟨𝒞⟩-terminal .HasTerminal.witness)

module interp-primitives (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
                         (Ω : Fam⟨𝒞⟩.Obj) (into-Ω : Fam⟨𝒞⟩.Mor Fam⟨𝒞⟩-bool Ω) where

  open Signature Sig
  open Interpretation ℐ
  open prop-setoid._⇒_ using (func; func-resp-≈)

  private
    module M-cat = Category M.cat
    module Fam⟨𝒞⟩-cat = Category Fam⟨𝒞⟩.cat
    module Fam⟨𝒞⟩-P = HasProducts Fam⟨𝒞⟩-products

  open Fam⟨𝒞⟩ using (simple[_,_]; simplef[_,_]; Obj; Mor)
  open Fam⟨𝒞⟩.products M-products using (simple-monoidal)
  open Fam⟨𝒞⟩.predicates M.terminal using (predicate)
  open indexed-family._⇒f_
  open Fam⟨𝒞⟩.Mor using (idxf; famf)

  private
    PF : PointedFPCat _ _ _
    PF = PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ]

  ⟦sort⟧′ : sort → Obj
  ⟦sort⟧′ s = simple[ sort-index s , sort-width s ]

  args : List sort → Obj
  args = PointedFPCat.list→product PF ⟦sort⟧′

  untuple : ∀ is → prop-setoid._⇒_ (Fam⟨𝒞⟩.Obj.idx (args is)) (sort-vals-setoid sort-index is)
  untuple []       .func _ = tt
  untuple (i ∷ is) .func (v , p) = v , untuple is .func p
  untuple []       .func-resp-≈ _ = prop.tt
  untuple (i ∷ is) .func-resp-≈ e = prop.proj₁ e prop., untuple is .func-resp-≈ (prop.proj₂ e)

  collect : ∀ is → Mor (args is) simple[ sort-vals-setoid sort-index is , bases-width is ]
  collect []       = simplef[ untuple [] , M-cat.id 0 ]
  collect (i ∷ is) = simple-monoidal Fam⟨𝒞⟩-cat.∘ Fam⟨𝒞⟩-P.prod-m (Fam⟨𝒞⟩-cat.id (⟦sort⟧′ i)) (collect is)

  op-mor : ∀ {is o} (ω : op is o) → Mor simple[ sort-vals-setoid sort-index is , bases-width is ] (⟦sort⟧′ o)
  op-mor ω .idxf = op-fun ω
  op-mor ω .famf .transf c = op-deps ω .func c
  op-mor ω .famf .natural {c} {c'} e =
    M-cat.≈-trans (M-cat.id-right {f = op-deps ω .func c'})
      (M-cat.≈-trans (M-cat.≈-sym (op-deps ω .func-resp-≈ e))
                  (M-cat.≈-sym (M-cat.id-left {f = op-deps ω .func c})))


  private
    PF′ : PointedFPCat _ _ _
    PF′ = PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Ω ]

  model-over : Model PF′ Sig
  model-over .Model.⟦sort⟧ = ⟦sort⟧′
  model-over .Model.⟦op⟧ {is} {o} ω = op-mor ω Fam⟨𝒞⟩-cat.∘ collect is
  model-over .Model.⟦rel⟧ {is} ψ = into-Ω Fam⟨𝒞⟩-cat.∘ predicate (rel-pred ψ ∘S untuple is)

  arg-collect = collect
