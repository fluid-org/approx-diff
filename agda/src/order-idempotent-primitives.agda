{-# OPTIONS --postfix-projections --prop --safe #-}

-- The interpretation of the primitives over families of position orders: a sort's fibre is the
-- discrete order of its width, and an operation's fibre map at a tuple of constants is its
-- dependency relation there, absorbed via the identity laws.
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
open import primitives using (Primitives; sort-vals-setoid)
import indexed-family
import matrix
import fam
import order-idempotent

module order-idempotent-primitives
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top

OI-products : HasProducts OI.cat
OI-products = biproducts→products OI.cmon OI.biproduct

module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ OI.cat

Fam⟨𝒞⟩-terminal = Fam⟨𝒞⟩.terminal OI.terminal
Fam⟨𝒞⟩-products = Fam⟨𝒞⟩.products.products OI-products
Fam⟨𝒞⟩-coproducts = Fam⟨𝒞⟩.coproducts

Fam⟨𝒞⟩-bool =
  Fam⟨𝒞⟩-coproducts .HasCoproducts.coprod
    (Fam⟨𝒞⟩-terminal .HasTerminal.witness)
    (Fam⟨𝒞⟩-terminal .HasTerminal.witness)

module interp-primitives (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  open Signature Sig
  open Primitives 𝒫
  open prop-setoid._⇒_ using (func; func-resp-≈)

  private
    module OIC = Category OI.cat
    module M = matrix.Mat S
    module FC = Category Fam⟨𝒞⟩.cat
    module FP = HasProducts Fam⟨𝒞⟩-products
    open Category.Iso

  open Fam⟨𝒞⟩ using (simple[_,_]; simplef[_,_]; Obj; Mor)
  open Fam⟨𝒞⟩.products OI-products using (simple-monoidal)
  open Fam⟨𝒞⟩.predicates OI.terminal using (predicate)
  open indexed-family._⇒f_
  open Fam⟨𝒞⟩.Mor using (idxf; famf)
  open OI using (mat; absorbed)

  private
    PF : PointedFPCat _ _ _
    PF = PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ]

  ⟦sort⟧′ : sort → Obj
  ⟦sort⟧′ s = simple[ sort-index s , OI.disc (sort-width s) ]

  args : List sort → Obj
  args = PointedFPCat.list→product PF ⟦sort⟧′

  -- Reassociate the index of the argument product into a tuple of constants.
  untuple : ∀ is → prop-setoid._⇒_ (Fam⟨𝒞⟩.Obj.idx (args is)) (sort-vals-setoid sort-index is)
  untuple []       .func _ = tt
  untuple (i ∷ is) .func (v , p) = v , untuple is .func p
  untuple []       .func-resp-≈ _ = prop.tt
  untuple (i ∷ is) .func-resp-≈ e = prop.proj₁ e prop., untuple is .func-resp-≈ (prop.proj₂ e)

  -- Collapse the argument product onto the discrete order of the summed widths.
  collect : ∀ is → Mor (args is) simple[ sort-vals-setoid sort-index is , OI.disc (bases-width is) ]
  collect []       = simplef[ untuple [] , OIC.id (OI.disc 0) ]
  collect (i ∷ is) =
    simplef[ idS _ , OI.disc-⊕ (sort-width i) (bases-width is) .fwd ]
      FC.∘ simple-monoidal
      FC.∘ FP.prod-m (FC.id (⟦sort⟧′ i)) (collect is)

  -- A dependency relation presented between discrete orders; absorption is the identity laws.
  matrix-morₘ : ∀ {m n} → Category._⇒_ M.cat m n → OI._⇒ₘ_ (OI.disc m) (OI.disc n)
  matrix-morₘ R .mat = R
  matrix-morₘ R .absorbed =
    OI.≈ₘ-trans (M.∘-cong (M.id-left {M = R}) (OI.≈ₘ-refl {M = M.I}))
                (M.id-right {M = R})

  matrix-mor : ∀ {m n} → Category._⇒_ M.cat m n → OI._⇒_ (OI.disc m) (OI.disc n)
  matrix-mor R = OI.mat→mor (matrix-morₘ R)

  matrix-mor-cong : ∀ {m n} {R R' : Category._⇒_ M.cat m n} →
                    Category._≈_ M.cat R R' → OIC._≈_ (matrix-mor R) (matrix-mor R')
  matrix-mor-cong {R = R} {R'} e =
    OI.mat→mor-congₘ {f = matrix-morₘ R} {g = matrix-morₘ R'} e

  op-mor : ∀ {is o} (ω : op is o) →
           Mor simple[ sort-vals-setoid sort-index is , OI.disc (bases-width is) ] (⟦sort⟧′ o)
  op-mor ω .idxf = op-fun ω
  op-mor ω .famf .transf c = matrix-mor (op-deps ω .func c)
  op-mor ω .famf .natural {c} {c'} e =
    OI.≈p-trans (OI.SMC.id-right {f = matrix-mor (op-deps ω .func c')})
      (OI.≈p-trans
        (OI.mat→mor-congₘ {f = matrix-morₘ (op-deps ω .func c')}
                          {g = matrix-morₘ (op-deps ω .func c)}
          (OI.≈ₘ-sym (op-deps ω .func-resp-≈ e)))
        (OI.≈p-sym (OI.SMC.id-left {f = matrix-mor (op-deps ω .func c)})))

  model : Model PF Sig
  model .Model.⟦sort⟧ = ⟦sort⟧′
  model .Model.⟦op⟧ {is} {o} ω = op-mor ω FC.∘ collect is
  model .Model.⟦rel⟧ {is} ψ = predicate (rel-pred ψ ∘S untuple is)

  -- The same interpretation over any object of truth values receiving the booleans. The argument
  -- product is rebuilt against the retargeted pointed category, whose list→product does not reduce
  -- at a neutral sort list, so the one at the original booleans cannot be reused.
  module over (Ω : Obj) (into-Ω : Mor Fam⟨𝒞⟩-bool Ω) where

    private
      PF′ : PointedFPCat _ _ _
      PF′ = PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Ω ]

      args′ : List sort → Obj
      args′ = PointedFPCat.list→product PF′ ⟦sort⟧′

      untuple′ : ∀ is → prop-setoid._⇒_ (Fam⟨𝒞⟩.Obj.idx (args′ is)) (sort-vals-setoid sort-index is)
      untuple′ []       .func _ = tt
      untuple′ (i ∷ is) .func (v , p) = v , untuple′ is .func p
      untuple′ []       .func-resp-≈ _ = prop.tt
      untuple′ (i ∷ is) .func-resp-≈ e = prop.proj₁ e prop., untuple′ is .func-resp-≈ (prop.proj₂ e)

      collect′ : ∀ is → Mor (args′ is) simple[ sort-vals-setoid sort-index is , OI.disc (bases-width is) ]
      collect′ []       = simplef[ untuple [] , OIC.id (OI.disc 0) ]
      collect′ (i ∷ is) =
        simplef[ idS _ , OI.disc-⊕ (sort-width i) (bases-width is) .fwd ]
          FC.∘ simple-monoidal
          FC.∘ FP.prod-m (FC.id (⟦sort⟧′ i)) (collect′ is)

    model-over : Model PF′ Sig
    model-over .Model.⟦sort⟧ = ⟦sort⟧′
    model-over .Model.⟦op⟧ {is} {o} ω = op-mor ω FC.∘ collect′ is
    model-over .Model.⟦rel⟧ {is} ψ = into-Ω FC.∘ predicate (rel-pred ψ ∘S untuple′ is)
