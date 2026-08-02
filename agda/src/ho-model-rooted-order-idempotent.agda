{-# OPTIONS --postfix-projections --prop --safe #-}

-- The rooted higher-order model at position orders: families over the position orders as the
-- first-order side, families over the supported semimodules as the model, the realisation as the
-- change of base, and the dominated products supplying the weak exponentials. The unit object is
-- the lifted terminal, so the unit value carries one root; the primitives are interpreted as in
-- the first-order model, with the relations' booleans injected under the roots.
open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; HasTerminal; HasCoproducts)
open import signature using (Signature; Model; PFPC[_,_,_,_])
open import primitives using (Primitives)
open import finite-product-functor using (preserve-chosen-terminal)
import fam-mu-lifting.in-map
import order-idempotent-supported
import ho-model-order-idempotent
import language-rooted-fo-interpretation

module ho-model-rooted-order-idempotent
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_; trans; sym; refl); open Setoid A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where

open order-idempotent-supported S ∨-idem ∧-idem ⊤-add-top public
module HMO = ho-model-order-idempotent S ∨-idem ∧-idem ⊤-add-top

open Category.IsIso
open SemiMod._≈m_

private
  module SC = Category SS.Sup.cat

-- The realisation preserves the chosen terminal: the empty order realises as the zero module.
𝓥F-preserve-terminal : preserve-chosen-terminal 𝓥F OI.terminal Sup-terminal
𝓥F-preserve-terminal .inverse = 𝓥-𝟘-bwd
𝓥F-preserve-terminal .f∘inverse≈id =
  HasTerminal.to-terminal-unique Sup-terminal
    (SC._∘_ (HasTerminal.to-terminal Sup-terminal) 𝓥-𝟘-bwd) (SC.id _)
𝓥F-preserve-terminal .inverse∘f≈id .*≈* .prop-setoid._≃m_.func-eq e = λ ()

module Fam⟨𝒞⟩μ = fam-mu-lifting.in-map 0ℓ 0ℓ OI.terminal OI.cmon OI.biproduct OF.Lp-lifting

private
  module FCμ = Category Fam⟨𝒞⟩μ.cat
  module FCC = HasCoproducts Fam⟨𝒞⟩μ.coproducts

-- The unit object: the lifted terminal, one root for the unit value.
𝟙F = HasTerminal.witness (Fam⟨𝒞⟩μ.terminal OI.terminal)

𝒞𝟙ty : Fam⟨𝒞⟩μ.Obj
𝒞𝟙ty = Fam⟨𝒞⟩μ.Lf 𝟙F

𝒞unit-pt : Fam⟨𝒞⟩μ.Mor 𝟙F 𝒞𝟙ty
𝒞unit-pt = Fam⟨𝒞⟩μ.injF

𝒞Bool = FCC.coprod (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty) (Fam⟨𝒞⟩μ.Lf 𝒞𝟙ty)

-- The rooted interpretation of the primitives: the first-order interpretation, with the
-- relations' booleans injected under the roots of the rooted booleans.
module rooted-primitives (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  private
    module IP = HMO.interp-primitives Sig 𝒫

  boolify : Fam⟨𝒞⟩μ.Mor HMO.Fam⟨𝒞⟩-bool 𝒞Bool
  boolify =
    FCC.coprod-m
      (FCμ._∘_ (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty}) (Fam⟨𝒞⟩μ.injF {X = 𝟙F}))
      (FCμ._∘_ (Fam⟨𝒞⟩μ.injF {X = 𝒞𝟙ty}) (Fam⟨𝒞⟩μ.injF {X = 𝟙F}))

  model : Model PFPC[ Fam⟨𝒞⟩μ.cat , Fam⟨𝒞⟩μ.terminal OI.terminal , Fam⟨𝒞⟩μ.products , 𝒞Bool ] Sig
  model = IP.over.model-over 𝒞Bool boolify

-- The rooted higher-order model and the first-order comparison at the realisation.
module rooted-interp (Sig : Signature 0ℓ) (𝒫 : Primitives S Sig) where

  open rooted-primitives Sig 𝒫

  open language-rooted-fo-interpretation Sig 0ℓ 0ℓ
    OI.terminal OI.cmon OI.biproduct OF.Lp-lifting
    Sup-terminal SS.Sup.cmon Sup-biproduct SS.supported-lifting
    𝓥F 𝓥F-preserve-terminal (λ {P} {Q} → 𝓥F-preserve-products {P} {Q})
    𝓥-Lp-iso (λ {P} {Q} f → Lmap-intertwine {P} {Q} f)
    SupExp.exponentials
    𝒞𝟙ty 𝒞unit-pt model
    public
