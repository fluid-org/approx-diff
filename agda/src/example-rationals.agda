{-# OPTIONS --prop --postfix-projections --safe #-}

module example-rationals where

open import categories using (Category; HasInitial; HasProducts; HasTerminal)
import cmon-enriched as CMon
import matrix-new
import semimodule
import ho-model-semimod
import indexed-family
import prop
import semiring-Q

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import prop using (liftS) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ) public
open import prop-setoid using (Setoid)
open Setoid using (Carrier) public
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import example-signature using (Sig; number; label; approx) public
import example
open import language-syntax Sig hiding (_,_) public
open example.ex public

module HM = ho-model-semimod semiring-Q.semiring
module FD = matrix-new.Mat semiring-Q.semiring
module SM = semimodule semiring-Q.semiring
module Sq = CommutativeSemiring semiring-Q.semiring
open CMon.CMonEnriched FD.cmon using (_+m_)
open FD using (_∷_; []) public

unitm : FD._⇒_ 0 1
unitm = HasInitial.from-initial FD.initial {1}
conjunctm : FD._⇒_ (HasProducts.prod FD.products 1 1) 1
conjunctm = HasProducts.p₁ FD.products {1} {1} +m HasProducts.p₂ FD.products {1} {1}

private
  module FDm = Category FD.cat
  module Add = CommutativeMonoid semiring-Q.additive
  module Mul = CommutativeMonoid semiring-Q.multiplicative

  num-zero : prop-setoid._⇒_ (prop-setoid.𝟙 {0ℓ} {0ℓ}) semiring-Q.setoid
  num-zero = record { func = λ _ → 0ℚ ; func-resp-≈ = λ _ → Sq.refl }

  num-add : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-add = record { func = λ (x , y) → Add._+_ x y ; func-resp-≈ = λ e → Add.+-cong (prop.proj₁ e) (prop.proj₂ e) }

  num-mult : prop-setoid._⇒_ (prop-setoid.⊗-setoid semiring-Q.setoid semiring-Q.setoid) semiring-Q.setoid
  num-mult = record { func = λ (x , y) → Mul._+_ x y ; func-resp-≈ = λ e → Mul.+-cong (prop.proj₁ e) (prop.proj₂ e) }

  scalar : ℚ → FD._⇒_ 1 1
  scalar c = record
    { func             = FD.scale c
    ; func-resp-≈      = FD.scale-cong {a = c} {a' = c} Sq.refl
    ; +-preserving     = FD.scale-+ {a = c}
    ; ε-preserving     = FD.scale-ε {a = c}
    ; scale-preserving = λ {a} {v} →
        FD.≈-trans (FD.≈-sym (FD.scale-· {a = c} {b = a} {v = v}))
          (FD.≈-trans (FD.scale-cong (Sq.·-comm {c} {a}) (FD.≈-refl {v = v}))
                      (FD.scale-· {a = a} {b = c} {v = v}))
    }

  scalar-cong : ∀ {x y} → Setoid._≈_ semiring-Q.setoid x y → scalar x FDm.≈ scalar y
  scalar-cong {x} (liftS refl) = FDm.≈-refl {f = scalar x}

open import example-signature-interpretation FD.cat FD.products FD.terminal 1 unitm conjunctm
  semiring-Q.setoid num-zero num-add num-mult public
module D = Deriv scalar scalar-cong
open HM.interp Sig D.BaseInterp1 public
open HM.interp-sd Sig D.BaseInterp1 using (ty-sd) public

open indexed-family._⇒f_ public
open SM._⇒_ public

mor : ∀ {Γ τ} (tm : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
mor tm env = ⟦ tm ⟧tm .famf .transf env

fwd : ∀ {Γ τ} (tm : Γ ⊢ τ) (env : ⟦ Γ ⟧ctxt .idx .Carrier) → _
fwd tm env = mor tm env .func
