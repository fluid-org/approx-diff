{-# OPTIONS --postfix-projections --prop --safe #-}

-- Interpretation of primitives over families of self-dual semimodules: sort's fibre is free
-- self-dual semimodule of its width, and operation's fibre map at tuple of constants is its
-- dependency relation there, read as morphism through matrix embedding.
open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Fin as Fin
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import prop-setoid using (Setoid; idS; _∘S_)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature; Model; PointedFPCat; PFPC[_,_,_,_])
open import categories using (Category; HasProducts; HasTerminal; HasCoproducts)
open import cmon-enriched using (biproduct-iso)
import prop
open prop using (_,_)
open import signature.interpretation using (Interpretation; sort-vals-setoid)
import indexed-family
import matrix
import matrix-embedding
import semimodule
import sd-semimodule
import fam

module sd-semimodule-primitives {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

module M = matrix.Mat S
module ME = matrix-embedding S
module SemiMod = semimodule S
module SDSemiMod = sd-semimodule S

open SDSemiMod using (S^_; S^-+; ⊕-iso)
open SDSemiMod.SelfDual using (obj)
open SDSemiMod._≅sd_ using (iso)
open Category SemiMod.cat using (Iso; IsIso→Iso; Iso-trans; ≈-refl; ≈-sym; ≈-trans; ∘-cong; id-left; id-right)
open Category.Iso
open SemiMod._≈m_
open prop-setoid._≃m_ using (func-eq)

ι1-iso : Iso (ME.𝔽 1) SemiMod.𝕀
ι1-iso .fwd = ME.ι1-fwd
ι1-iso .bwd = ME.ι1-bwd
ι1-iso .fwd∘bwd≈id .*≈* .func-eq e = e
ι1-iso .bwd∘fwd≈id .*≈* .func-eq e Fin.zero = e Fin.zero

-- Free semimodule of width n coincides with underlying object of free self-dual semimodule:
-- iterated biproducts agree with vectors up to comparison isomorphism.
𝔽≅S^ : ∀ n → Iso (ME.𝔽 n) (obj (S^ n))
𝔽≅S^ zero = IsIso→Iso ME.𝔽F-preserve-terminal
𝔽≅S^ (suc zero) = ι1-iso
𝔽≅S^ (suc (suc n)) =
  Iso-trans
    (IsIso→Iso (biproduct-iso SemiMod.cmon-enriched
                  (ME.𝔽-biproduct 1 (suc n))
                  (SemiMod.biproduct (ME.𝔽 1) (ME.𝔽 (suc n)))))
    (⊕-iso ι1-iso (𝔽≅S^ (suc n)))

-- Dependency relation as morphism between free objects.
matrix-mor : ∀ {m n} → Category._⇒_ M.cat m n → SemiMod._⇒_ (obj (S^ m)) (obj (S^ n))
matrix-mor {m} {n} R = 𝔽≅S^ n .fwd SemiMod.∘ (ME.mat R SemiMod.∘ 𝔽≅S^ m .bwd)

matrix-mor-cong : ∀ {m n} {R R' : Category._⇒_ M.cat m n} →
                  Category._≈_ M.cat R R' → SemiMod._≈m_ (matrix-mor R) (matrix-mor R')
matrix-mor-cong {m} {n} e =
  ∘-cong (≈-refl {f = 𝔽≅S^ n .fwd}) (∘-cong (ME.mat-cong e) (≈-refl {f = 𝔽≅S^ m .bwd}))

module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ SDSemiMod.cat

Fam⟨𝒞⟩-terminal = Fam⟨𝒞⟩.terminal SDSemiMod.terminal
Fam⟨𝒞⟩-products = Fam⟨𝒞⟩.products.products SDSemiMod.products
Fam⟨𝒞⟩-coproducts = Fam⟨𝒞⟩.coproducts

Fam⟨𝒞⟩-bool =
  Fam⟨𝒞⟩-coproducts .HasCoproducts.coprod
    (Fam⟨𝒞⟩-terminal .HasTerminal.witness)
    (Fam⟨𝒞⟩-terminal .HasTerminal.witness)

-- Dependency data of interpretation read as morphisms at free objects: form consumed by
-- operational semantics.
module interp-deps {ℓ} (Sig : Signature ℓ) (ℐ : Interpretation S Sig) where

  open Signature Sig
  open Interpretation ℐ
  open prop-setoid._⇒_ using (func)

  op-dep : ∀ {is o'} (ω : op is o') (vs : sort-vals is) →
           SemiMod._⇒_ (ME.𝔽 (bases-width is)) (ME.𝔽 (sort-width o'))
  op-dep ω vs = ME.mat (op-deps ω .func vs)

  rel-dep : ∀ {is} (ψ : rel is) (vs : sort-vals is) →
            SemiMod._⇒_ (ME.𝔽 (bases-width is)) (ME.𝔽 1)
  rel-dep ψ vs = ME.mat (rel-deps ψ .func vs)

module interp-primitives (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
                         (Ω : Fam⟨𝒞⟩.Obj) (into-Ω : Fam⟨𝒞⟩.Mor Fam⟨𝒞⟩-bool Ω) where

  open Signature Sig
  open Interpretation ℐ
  open prop-setoid._⇒_ using (func; func-resp-≈)

  private
    module SD-cat = Category SDSemiMod.cat
    module Fam⟨𝒞⟩-cat = Category Fam⟨𝒞⟩.cat
    module Fam⟨𝒞⟩-P = HasProducts Fam⟨𝒞⟩-products

  open Fam⟨𝒞⟩ using (simple[_,_]; simplef[_,_]; Obj; Mor)
  open Fam⟨𝒞⟩.products SDSemiMod.products using (simple-monoidal)
  open Fam⟨𝒞⟩.predicates SDSemiMod.terminal using (predicate)
  open indexed-family._⇒f_
  open Fam⟨𝒞⟩.Mor using (idxf; famf)

  private
    PF : PointedFPCat _ _ _
    PF = PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Fam⟨𝒞⟩-bool ]

  ⟦sort⟧′ : sort → Obj
  ⟦sort⟧′ s = simple[ sort-index s , S^ (sort-width s) ]

  args : List sort → Obj
  args = PointedFPCat.list→product PF ⟦sort⟧′

  untuple : ∀ is → prop-setoid._⇒_ (Fam⟨𝒞⟩.Obj.idx (args is)) (sort-vals-setoid sort-index is)
  untuple []       .func _ = tt
  untuple (i ∷ is) .func (v , p) = v , untuple is .func p
  untuple []       .func-resp-≈ _ = prop.tt
  untuple (i ∷ is) .func-resp-≈ e = prop.proj₁ e prop., untuple is .func-resp-≈ (prop.proj₂ e)

  collect : ∀ is → Mor (args is) simple[ sort-vals-setoid sort-index is , S^ (bases-width is) ]
  collect []       = simplef[ untuple [] , SD-cat.id (S^ 0) ]
  collect (i ∷ is) =
    simplef[ idS _ , S^-+ (sort-width i) (bases-width is) .iso .fwd ]
      Fam⟨𝒞⟩-cat.∘ simple-monoidal
      Fam⟨𝒞⟩-cat.∘ Fam⟨𝒞⟩-P.prod-m (Fam⟨𝒞⟩-cat.id (⟦sort⟧′ i)) (collect is)

  op-mor : ∀ {is o} (ω : op is o) →
           Mor simple[ sort-vals-setoid sort-index is , S^ (bases-width is) ] (⟦sort⟧′ o)
  op-mor ω .idxf = op-fun ω
  op-mor ω .famf .transf c = matrix-mor (op-deps ω .func c)
  op-mor ω .famf .natural {c} {c'} e =
    ≈-trans (id-right {f = matrix-mor (op-deps ω .func c')})
      (≈-trans (matrix-mor-cong (Category.≈-sym M.cat (op-deps ω .func-resp-≈ e)))
               (≈-sym (id-left {f = matrix-mor (op-deps ω .func c)})))

  private
    PF′ : PointedFPCat _ _ _
    PF′ = PFPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩-terminal , Fam⟨𝒞⟩-products , Ω ]

  model-over : Model PF′ Sig
  model-over .Model.⟦sort⟧ = ⟦sort⟧′
  model-over .Model.⟦op⟧ {is} {o} ω = op-mor ω Fam⟨𝒞⟩-cat.∘ collect is
  model-over .Model.⟦rel⟧ {is} ψ = into-Ω Fam⟨𝒞⟩-cat.∘ predicate (rel-pred ψ ∘S untuple is)

  arg-collect = collect
