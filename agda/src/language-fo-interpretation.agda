{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (Level)
open import Data.List using (List)
open import prop-setoid using (𝟙)
open import every using (Every; []; _∷_)
open import signature using (Signature; FPC[_,_,_]; PointedFPCat; PFPC[_,_]; Model)
  renaming (module PointedFPCat to PFPC)
open import categories using (Category; HasProducts; HasCoproducts; HasTerminal; HasStrongCoproducts; HasLists)
import fam
import language-syntax

module language-fo-interpretation
  {o m e ℓ} (Sig : Signature ℓ)
  (os es : Level)
  (𝒞 : Category o m e)
  (𝒞-terminal : HasTerminal 𝒞)
  (𝒞-products : HasProducts 𝒞)
  where

open Signature Sig public
open language-syntax Sig public
module Fam⟨𝒞⟩ = fam.CategoryOfFamilies os es 𝒞
open Category Fam⟨𝒞⟩.cat using (_⇒_; _∘_; id) public
-- HasTerminal's `to-terminal` is kept local (not re-exported), so downstream
-- consumers can open another HasTerminal (e.g. MatRep's) without clashing.
open HasTerminal (Fam⟨𝒞⟩.terminal 𝒞-terminal) using () renaming (witness to ⟦unit⟧) public
open HasTerminal (Fam⟨𝒞⟩.terminal 𝒞-terminal) using (to-terminal)
open HasCoproducts Fam⟨𝒞⟩.coproducts using () renaming (coprod to _⟦+⟧_) public
open HasCoproducts Fam⟨𝒞⟩.coproducts using (in₁; in₂)
open HasProducts (Fam⟨𝒞⟩.products.products 𝒞-products)
  using () renaming (prod to _⟦×⟧_; pair to ⟨_,_⟩) public
open HasProducts (Fam⟨𝒞⟩.products.products 𝒞-products) using (p₁; p₂)
open HasStrongCoproducts (Fam⟨𝒞⟩.products.strongCoproducts 𝒞-products)
  using () renaming (copair to [_,_]) public
open HasLists (Fam⟨𝒞⟩.lists 𝒞-terminal 𝒞-products)
  renaming (list to ⟦list⟧; nil to ⟦nil⟧; cons to ⟦cons⟧; fold to ⟦fold⟧) public

𝟚 : Fam⟨𝒞⟩.Obj
𝟚 = ⟦unit⟧ ⟦+⟧ ⟦unit⟧

PFPC : PointedFPCat _ _ _
PFPC = PFPC[ FPC[ Fam⟨𝒞⟩.cat , Fam⟨𝒞⟩.terminal 𝒞-terminal , Fam⟨𝒞⟩.products.products 𝒞-products ] , 𝟚 ]

module Interpretation (M : Model PFPC Sig) where
  open Model M public

  ⟦_⟧ty : type → Fam⟨𝒞⟩.Obj
  ⟦ unit ⟧ty = ⟦unit⟧
  ⟦ base s ⟧ty = ⟦sort⟧ s
  ⟦ τ₁ [×] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦×⟧ ⟦ τ₂ ⟧ty
  ⟦ τ₁ [+] τ₂ ⟧ty = ⟦ τ₁ ⟧ty ⟦+⟧ ⟦ τ₂ ⟧ty
  ⟦ list τ ⟧ty = ⟦list⟧ ⟦ τ ⟧ty

  ⟦_⟧ctxt : ctxt → Fam⟨𝒞⟩.Obj
  ⟦ emp ⟧ctxt = ⟦unit⟧
  ⟦ Γ · τ ⟧ctxt = ⟦ Γ ⟧ctxt ⟦×⟧ ⟦ τ ⟧ty

  ⟦_⟧bases-list : List sort → Fam⟨𝒞⟩.Obj
  ⟦_⟧bases-list = PFPC.list→product PFPC ⟦sort⟧

  ⟦_⟧var : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
  ⟦_⟧var {Γ · τ}  zero     = p₂ {⟦ Γ ⟧ctxt} {⟦ τ ⟧ty}
  ⟦_⟧var {Γ · τ'} (succ x) = ⟦ x ⟧var ∘ p₁ {⟦ Γ ⟧ctxt} {⟦ τ' ⟧ty}

  ⟦_⟧tm    : ∀ {Γ τ}  → Γ ⊢ τ → ⟦ Γ ⟧ctxt ⇒ ⟦ τ ⟧ty
  ⟦_⟧bases : ∀ {Γ σs} → Every (λ σ → Γ ⊢ base σ) σs → ⟦ Γ ⟧ctxt ⇒ ⟦ σs ⟧bases-list

  ⟦ var x ⟧tm = ⟦ x ⟧var
  ⟦ unit ⟧tm = to-terminal
  ⟦ inl M ⟧tm = in₁ ∘ ⟦ M ⟧tm
  ⟦ inr M ⟧tm = in₂ ∘ ⟦ M ⟧tm
  ⟦ case M N₁ N₂ ⟧tm = [ ⟦ N₁ ⟧tm , ⟦ N₂ ⟧tm ] ∘ ⟨ id _ , ⟦ M ⟧tm ⟩
  ⟦ pair M N ⟧tm = ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fst M ⟧tm = p₁ ∘ ⟦ M ⟧tm
  ⟦ snd M ⟧tm = p₂ ∘ ⟦ M ⟧tm
  ⟦ bop ω Ms ⟧tm = ⟦op⟧ ω ∘ ⟦ Ms ⟧bases
  ⟦ brel ω Ms ⟧tm = ⟦rel⟧ ω ∘ ⟦ Ms ⟧bases
  ⟦ nil ⟧tm = ⟦nil⟧ ∘ to-terminal
  ⟦ cons M N ⟧tm = ⟦cons⟧ ∘ ⟨ ⟦ M ⟧tm , ⟦ N ⟧tm ⟩
  ⟦ fold M₁ M₂ M ⟧tm = ⟦fold⟧ ⟦ M₁ ⟧tm ⟦ M₂ ⟧tm ∘ ⟨ id _ , ⟦ M ⟧tm ⟩

  ⟦ [] ⟧bases = to-terminal
  ⟦ M ∷ Ms ⟧bases = ⟨ ⟦ M ⟧tm , ⟦ Ms ⟧bases ⟩
