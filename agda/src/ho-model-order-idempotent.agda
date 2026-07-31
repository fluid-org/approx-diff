{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model with position orders as the first-order model: families over the
-- order-idempotent category, interpreted in Fam(SemiMod S) via the splitting functor 𝓚. Sorts
-- carry discrete orders, where absorption is trivial, so the free first-order model is the
-- special case.
open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import prop-setoid using (Setoid; idS; _∘S_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import categories using (Category; HasProducts; HasTerminal)
open import cmon-enriched using (biproducts→products)
open import functor using (Functor)
import prop
open prop using (_,_)
open import primitives using (Primitives; sort-vals-setoid)
import indexed-family
import semimodule
import matrix
import order-idempotent
import order-idempotent-embedding-semimod
import ho-model

module ho-model-order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

module SemiMod = semimodule S
module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top
module OIES = order-idempotent-embedding-semimod S ∨-idem ∧-idem ⊤-add-top

-- The chosen products on the order-idempotent category, from its biproducts.
OI-products : HasProducts OI.cat
OI-products = biproducts→products OI.cmon OI.biproduct

open ho-model.Interpretation
  OI.cat OI.terminal OI-products
  SemiMod.cat SemiMod.cmon-enriched SemiMod.limits SemiMod.terminal SemiMod.biproduct
  OIES.𝓚 OIES.𝓚-preserve-terminal (λ {X} {Y} → OIES.𝓚-preserve-products {X} {Y})
  (λ {a} {b} {g₁} {g₂} h → OIES.𝓚-faithful {a} {b} {g₁} {g₂} h) (λ h _ → OIES.𝓚-full h)
  public

-- The interpretation of the primitives: a sort's fibre is the discrete order of its width, and an
-- operation's fibre map at a tuple of constants is its dependency relation there, absorbed via the
-- identity laws.
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

  -- A dependency relation as a morphism between discrete orders; absorption is the identity laws.
  matrix-mor : ∀ {m n} → Category._⇒_ M.cat m n → OI._⇒_ (OI.disc m) (OI.disc n)
  matrix-mor R .mat = R
  matrix-mor R .absorbed =
    OI.≈ₘ-trans (M.∘-cong (M.id-left {M = R}) (OI.≈ₘ-refl {M = M.I}))
                (M.id-right {M = R})

  matrix-mor-cong : ∀ {m n} {R R' : Category._⇒_ M.cat m n} →
                    Category._≈_ M.cat R R' → OIC._≈_ (matrix-mor R) (matrix-mor R')
  matrix-mor-cong e = e

  model : Model PF Sig
  model .Model.⟦sort⟧ = ⟦sort⟧′
  model .Model.⟦op⟧ {is} {o} ω = opω FC.∘ collect is
    where
    opω : Mor simple[ sort-vals-setoid sort-index is , OI.disc (bases-width is) ] (⟦sort⟧′ o)
    opω .idxf = op-fun ω
    opω .famf .transf c = matrix-mor (op-deps ω .func c)
    opω .famf .natural {c} {c'} e =
      OI.≈ₘ-trans (M.id-right {M = op-deps ω .func c'})
        (OI.≈ₘ-trans (OI.≈ₘ-sym (op-deps ω .func-resp-≈ e))
                     (OI.≈ₘ-sym (M.id-left {M = op-deps ω .func c})))
  model .Model.⟦rel⟧ {is} ψ = predicate (rel-pred ψ ∘S untuple is)
