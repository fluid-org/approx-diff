{-# OPTIONS --postfix-projections --prop --safe #-}

-- The higher-order model with SDSemiMod as the first-order model: families over self-dual
-- semimodules, interpreted in Fam(SemiMod S) via the forgetful functor U.
open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import prop-setoid using (Setoid; idS; _∘S_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import categories using (Category; HasProducts)
open import functor using (Functor)
open import Relation.Binary.PropositionalEquality using (refl)
import prop
open prop using (_,_)
open import primitives using (Primitives; sort-vals-setoid)
import language-syntax
import indexed-family
import semimodule
import sd-semimodule
import matrix
import matrix-embedding-semimod
import ho-model

module ho-model-sd-semimod {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module SemiMod = semimodule S
module SDSemiMod = sd-semimodule S

open ho-model.Interpretation
  SDSemiMod.cat SDSemiMod.terminal SDSemiMod.products
  SemiMod.cat SemiMod.cmon-enriched SemiMod.limits SemiMod.terminal SemiMod.biproduct
  SDSemiMod.U SDSemiMod.U-preserve-terminal (λ {X} {Y} → SDSemiMod.U-preserve-products {X} {Y})
  (λ e → e) (λ h _ → h , Category.≈-refl SemiMod.cat)
  public


-- The interpretation of the primitives: a sort's fibre is the free object of its width, and an
-- operation's fibre map at a tuple of constants is its dependency relation there, read as a morphism
-- through the matrix embedding.
module interp-primitives (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  open Signature Sig
  open Primitives 𝒫
  open prop-setoid._⇒_ using (func; func-resp-≈)

  private
    module SM = Category SemiMod.cat
    module M = matrix.Mat S
    module MES = matrix-embedding-semimod S
    module FC = Category Fam⟨𝒞⟩.cat
    module FP = HasProducts Fam⟨𝒞⟩-products
    open Category.Iso

  open Fam⟨𝒞⟩ using (simple[_,_]; simplef[_,_]; Obj; Mor)
  open Fam⟨𝒞⟩.products SDSemiMod.products using (simple-monoidal)
  open Fam⟨𝒞⟩.predicates SDSemiMod.terminal using (predicate)
  open indexed-family._⇒f_
  open Fam⟨𝒞⟩.Mor using (idxf; famf)

  private
    PF : PointedFPCat _ _ _
    PF = PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ]

  ⟦sort⟧′ : sort → Obj
  ⟦sort⟧′ s = simple[ sort-index s , SDSemiMod.S^ (sort-width s) ]

  args : List sort → Obj
  args = PointedFPCat.list→product PF ⟦sort⟧′

  -- Reassociate the index of the argument product into a tuple of constants.
  untuple : ∀ is → prop-setoid._⇒_ (Fam⟨𝒞⟩.Obj.idx (args is)) (sort-vals-setoid sort-index is)
  untuple []       .func _ = tt
  untuple (i ∷ is) .func (v , p) = v , untuple is .func p
  untuple []       .func-resp-≈ _ = prop.tt
  untuple (i ∷ is) .func-resp-≈ e = prop.proj₁ e prop., untuple is .func-resp-≈ (prop.proj₂ e)

  -- Collapse the argument product onto the free object of the summed widths.
  collect : ∀ is → Mor (args is) simple[ sort-vals-setoid sort-index is , SDSemiMod.S^ (bases-width is) ]
  collect []       = simplef[ untuple [] , Category.id SDSemiMod.cat (SDSemiMod.S^ 0) ]
  collect (i ∷ is) =
    simplef[ idS _ , SDSemiMod.S^-+ (sort-width i) (bases-width is) .SDSemiMod._≅sd_.iso .fwd ]
      FC.∘ simple-monoidal
      FC.∘ FP.prod-m (FC.id (⟦sort⟧′ i)) (collect is)

  -- A dependency relation as a morphism between free objects.
  matrix-mor : ∀ {m n} → Category._⇒_ M.cat m n →
               SM._⇒_ (SDSemiMod.SelfDual.obj (SDSemiMod.S^ m)) (SDSemiMod.SelfDual.obj (SDSemiMod.S^ n))
  matrix-mor {m} {n} R =
    MES.X^≅S^ n .fwd SM.∘ (Functor.fmor MES.mat→mor R SM.∘ MES.X^≅S^ m .bwd)

  matrix-mor-cong : ∀ {m n} {R R' : Category._⇒_ M.cat m n} →
                    Category._≈_ M.cat R R' → SM._≈_ (matrix-mor R) (matrix-mor R')
  matrix-mor-cong {m} {n} e =
    SM.∘-cong (SM.≈-refl {f = MES.X^≅S^ n .fwd})
      (SM.∘-cong (Functor.fmor-cong MES.mat→mor e) (SM.≈-refl {f = MES.X^≅S^ m .bwd}))

  model : Model PF Sig
  model .Model.⟦sort⟧ = ⟦sort⟧′
  model .Model.⟦op⟧ {is} {o} ω = opω FC.∘ collect is
    where
    opω : Mor simple[ sort-vals-setoid sort-index is , SDSemiMod.S^ (bases-width is) ] (⟦sort⟧′ o)
    opω .idxf = op-fun ω
    opω .famf .transf c = matrix-mor (op-deps ω .func c)
    opω .famf .natural {c} {c'} e =
      SM.≈-trans SM.id-right
        (SM.≈-trans (matrix-mor-cong (Category.≈-sym M.cat (op-deps ω .func-resp-≈ e)))
                    (SM.≈-sym SM.id-left))
  model .Model.⟦rel⟧ {is} ψ = predicate (rel-pred ψ ∘S untuple is)

-- Self-dualities on the first-order types of the language with general
-- recursive types: instantiate the generic fibre-object machinery at the
-- self-dual semimodules.
module interp-sd (Sig : Signature 0ℓ)
                   (Impl : Model PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ] Sig)
   where

  open interp Sig Impl public
  open language-syntax Sig using (_⊢_)
  open SDSemiMod using (SelfDual; 𝟘; _⊕_) public
  open Setoid using (Carrier)

  open SemiMod._⇒_ using (func)

  -- Forward analysis: feed an input tangent, read the output tangent.
  fwd : ∀ {Γ τ} (M : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
  fwd M env = mor M env .func
