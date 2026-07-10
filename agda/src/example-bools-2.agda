{-# OPTIONS --prop --postfix-projections --safe #-}

-- Backward analyses of the list and rose-tree examples for the language with
-- general recursive types, over the self-dual Boolean algebras.

module example-bools-2 where

open import Level using (lift)
import Data.Fin as Fin
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit renaming (tt to ·) using ()
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import prop-setoid using (Setoid)
open Setoid using (Carrier)
import nat
open import example.signature nat.ℕ using (Sig; number; label)
open import label using (a; b)
import two
open import two renaming (I to ⊤; O to ⊥) using ()
import example.bool
import ho-model-boolalg-sd-semimod
import example-2
import indexed-family
import galois
import preorder

module HB = ho-model-boolalg-sd-semimod two.semiring two.semiring-boolean
module Ex2 = example-2 nat.ℕ nat.zero

open HB.interp-boolean-2 Sig example.bool.D.BaseInterp1
open indexed-family._⇒f_ using (transf)
open galois._⇒g_ using (right)
open preorder._=>_ using (fun)

open Ex2.L using (list; base; unit; var; μ; _[×]_; _[+]_; first-order)
open Ex2.ex using (query; rose; rose-query)

module T = HB.Fam⟨𝒟⟩-μ.Tree {n = 0} (λ ())

input : ⟦ list (base label [×] base number) ⟧ty (λ ()) .idx .Carrier
input = T.sup (inj₂ ((a , 0) , T.sup (inj₂ ((b , 1) , T.sup (inj₂ ((a , 1) , T.sup (inj₁ (lift ·))))))))

list-fo : first-order (list (base label [×] base number))
list-fo = μ (unit [+] ((base label [×] base number) [×] var Fin.zero))

bwd-slice : label.label → _
bwd-slice l =
  to-gal (𝟘 ⊕ ty₀ list-fo input) (ty₀ (base number) 0)
         (⟦ query l ⟧tm .famf .transf (_ , input)) .right .fun ⊥

-- Querying for the 'a' label uses the 1st and 3rd numbers.
test1 : bwd-slice a ≡ (lift · , (lift · , ⊥) , (lift · , ⊤) , (lift · , ⊥) , _)
test1 = ≡-refl

-- Querying for the 'b' label uses the 2nd number.
test2 : bwd-slice b ≡ (lift · , (lift · , ⊤) , (lift · , ⊥) , (lift · , ⊤) , _)
test2 = ≡-refl

-- Rose tree node 1 [node 2 [] , node 3 []]: the children lists are trees of a
-- nested μ-type, so folding over the tree exercises the nested recursion.
rose-input : ⟦ rose ⟧ty (λ ()) .idx .Carrier
rose-input =
  T.sup (1 , T.sup (inj₂ (T.sup (2 , T.sup (inj₁ (lift ·))) ,
             T.sup (inj₂ (T.sup (3 , T.sup (inj₁ (lift ·))) , T.sup (inj₁ (lift ·)))))))

rose-fo : first-order rose
rose-fo = μ (base number [×] μ (unit [+] (var (Fin.suc Fin.zero) [×] var Fin.zero)))

rose-bwd : _
rose-bwd =
  to-gal (𝟘 ⊕ ty₀ rose-fo rose-input) (ty₀ (base number) 0)
         (⟦ rose-query ⟧tm .famf .transf (_ , rose-input)) .right .fun ⊥

-- Summing demands every number in the tree.
rose-test : rose-bwd ≡ (lift · , ⊥ , (⊥ , _) , (⊥ , _) , _)
rose-test = ≡-refl
