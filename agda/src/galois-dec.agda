{-# OPTIONS --postfix-projections --safe --prop #-}

-- Experimental sketch: Galois objects with decidable bottom. Each Obj here is
-- a `galois.Obj` together with a decision procedure for "is this element ⊥?"
-- on the underlying carrier. Used to enable a `force : 𝕃 X ⇒g X` morphism
-- (and thus a PointedMonad instance on 𝕃), since force needs to dispatch
-- between "this value is ⊥" (map to `bottom` in 𝕃 X) and "not ⊥" (map to <·>).

open import Level using (suc; 0ℓ)
open import Relation.Nullary using (Dec)
open import preorder using (Preorder)
open import join-semilattice using (JoinSemilattice)
open import galois using (Obj)

module galois-dec where

------------------------------------------------------------------------------
-- Set-level wrapper around the Prop-valued `_≃_ ⊥J`, so we can use the
-- standard `Dec` (which operates on Set-level predicates).
record Is-⊥ (X : Obj) (x : Obj.carrier X .Preorder.Carrier) : Set where
  constructor witness
  open Obj X using (carrier; joins)
  open Preorder carrier using (_≃_)
  open JoinSemilattice joins renaming (⊥ to ⊥J)
  field
    eq : x ≃ ⊥J

------------------------------------------------------------------------------
-- A Galois object with decidable bottom on its underlying carrier.
record Obj-dec : Set (suc 0ℓ) where
  field
    obj         : Obj
    ⊥-decidable : (x : Obj.carrier obj .Preorder.Carrier) → Dec (Is-⊥ obj x)
  open Obj obj public

------------------------------------------------------------------------------
-- Forgetful map back to plain Galois.
forget : Obj-dec → Obj
forget = Obj-dec.obj

------------------------------------------------------------------------------
-- Pending: a `force : 𝕃 X ⇒g X` construction using ⊥-decidable.
--
--   force.right : 𝕃X.meets → X.meets
--     bottom ↦ X.joins.⊥
--     <x>    ↦ x
--   force.left : X.joins → 𝕃X.joins
--     y ↦ bottom    if ⊥-decidable y returns "y ≃ ⊥"
--     y ↦ <y>       otherwise
--   left⊣right: case-analysis on ⊥-decidable.
--
-- Once force is defined, we can package as `PointedMonad (galois.products)`
-- (after lifting all the existing 𝕃 structure to this wrapper).
