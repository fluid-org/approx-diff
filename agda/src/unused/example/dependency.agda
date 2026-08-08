{-# OPTIONS --prop --postfix-projections --safe #-}

module example.dependency where

import ho-model-sd-semimod
import semimodule
import indexed-family
import two

open import example.primitives public

open import Level using (lift; 0ℓ) public
open import Data.Unit renaming (tt to ·) using () public
open import Data.Product using (_,_) public
open import Data.Sum using (inj₁; inj₂) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Data.Integer using (+_; -[1+_]) public
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _/_) public
open import Data.Nat.Base public using (nonZero)
open import prop-setoid using (Setoid; IsEquivalence)
open Setoid using (Carrier) public
import example
open import language-syntax Sig hiding (_,_) public
module Ex = example ℚ 0ℚ
open Ex.ex public
open import label using (a; b) public

-- The model determined by the primitives, and the interpretation of the language over it.
module HM = ho-model-sd-semimod two.semiring
module PI = HM.interp-primitives Sig primitives
open HM.interp-sd Sig PI.model public

-- W-trees indexing the fibres of closed μ-types, for writing inputs.
module T = Pm.Tree {n = 0} (λ ())

module SemiMod-𝟚 = semimodule two.semiring
open indexed-family._⇒f_ public
open SemiMod-𝟚._⇒_ public
