{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (Level; 0ℓ)
open import categories using (Category; HasProducts; HasTerminal)

module example-signature-interpretation
  {o m e : Level}
  (𝒞 : Category o m e)
  (𝒞-products : HasProducts 𝒞)
  (𝒞-terminal : HasTerminal 𝒞)
  (TWO : Category.obj 𝒞)
  (unit-mor : Category._⇒_ 𝒞 (HasTerminal.witness 𝒞-terminal) TWO)
  (conjunct : Category._⇒_ 𝒞 (HasProducts.prod 𝒞-products TWO TWO) TWO)
  where

private
  module 𝒞 = Category 𝒞
  𝟙-base = HasTerminal.witness 𝒞-terminal
  to-𝟙-base : ∀ {X} → X 𝒞.⇒ 𝟙-base
  to-𝟙-base = HasTerminal.to-terminal 𝒞-terminal

open import Data.Sum using (inj₁; inj₂)
open import prop-setoid using (Setoid)
  renaming (_⇒_ to _⇒s_; ⊗-setoid to _×ₛ_; +-setoid to _+ₛ_; 𝟙 to 𝟙ₛ)
open import indexed-family using (module _⇒f_; Fam)
open import example-signature using (Sig)
import fam

open import language-fo-interpretation Sig 0ℓ 0ℓ 𝒞 𝒞-terminal 𝒞-products
  public

private
  module C = Category Fam⟨𝒞⟩.cat
  open Fam⟨𝒞⟩ using (Mor; simple[_,_]; simplef[_,_])
  open Fam⟨𝒞⟩.products 𝒞-products
    using (simple-monoidal)
  open HasProducts (Fam⟨𝒞⟩.products.products 𝒞-products) using (p₁; p₂)

  𝟚ₛ : Setoid 0ℓ 0ℓ
  𝟚ₛ = 𝟙ₛ +ₛ 𝟙ₛ

  open Fam⟨𝒞⟩.Obj
  open Fam
  open _⇒s_

  predicate-transf : ∀ X x y → X .fam .fm x 𝒞.⇒ 𝟚 .fam .fm y
  predicate-transf X x (inj₁ _) = to-𝟙-base
  predicate-transf X x (inj₂ _) = to-𝟙-base

  predicate-natural : ∀ X {x₁} {x₂} {y₁} {y₂}
    (x-eq : X .idx .Setoid._≈_ x₁ x₂)
    (y-eq : 𝟚ₛ .Setoid._≈_ y₁ y₂) →
    𝒞._≈_ (𝒞._∘_ (predicate-transf X x₂ y₂) (X .fam .subst x-eq))
          (𝒞._∘_ (𝟚 .fam .subst {y₁} {y₂} y-eq) (predicate-transf X x₁ y₁))
  predicate-natural X {x₁} {x₂} {inj₁ _} {inj₁ _} _ _ = HasTerminal.to-terminal-unique 𝒞-terminal _ _
  predicate-natural X {x₁} {x₂} {inj₂ _} {inj₂ _} _ _ = HasTerminal.to-terminal-unique 𝒞-terminal _ _

binary : ∀ {X G} → (Fam⟨𝒞⟩.simple[ X , G ] ⟦×⟧ (Fam⟨𝒞⟩.simple[ X , G ] ⟦×⟧ ⟦unit⟧)) C.⇒ Fam⟨𝒞⟩.simple[ X ×ₛ X , HasProducts.prod 𝒞-products G G ]
binary = simple-monoidal C.∘ ⟨ p₁ , (p₁ C.∘ p₂) ⟩

predicate : ∀ {X} → Fam⟨𝒞⟩.Obj.idx X ⇒s 𝟚ₛ → X C.⇒ 𝟚
predicate f .Mor.idxf = f
predicate {X} f .Mor.famf ._⇒f_.transf x = predicate-transf X x (f ._⇒s_.func x)
predicate {X} f .Mor.famf ._⇒f_.natural {x₁} {x₂} x₁≈x₂ =
  predicate-natural X {y₁ = f ._⇒s_.func x₁} x₁≈x₂ (f ._⇒s_.func-resp-≈ x₁≈x₂)

------------------------------------------------------------------------
-- Canonical interpretation of the example signature, parametric over the chosen TWO object plus its
-- `unit-mor` and `conjunct` morphisms. ⟦sort⟧-𝒞 is also exposed: trace-driven consumers need the
-- underlying 𝒞-level interpretation of sort directly.

open import signature using (Signature; Model)
open import example-signature using (Sig; number; label; add; mult; lbl; equal-label)
  renaming (zero to op-zero) public
import nat
import label as Lbl
open import prop-setoid using () renaming (const to constₛ)

⟦sort⟧-𝒞 : Signature.sort Sig → Category.obj 𝒞
⟦sort⟧-𝒞 number = TWO
⟦sort⟧-𝒞 label  = 𝟙-base

BaseInterp : Model PFPC Sig
BaseInterp .Model.⟦sort⟧ s           = simple[ ⟦sort⟧-idx s , ⟦sort⟧-𝒞 s ]
  where
    ⟦sort⟧-idx : Signature.sort Sig → Setoid 0ℓ 0ℓ
    ⟦sort⟧-idx number = nat.ℕₛ
    ⟦sort⟧-idx label  = Lbl.Label
BaseInterp .Model.⟦op⟧ op-zero       = simplef[ nat.zero-m , unit-mor ]
BaseInterp .Model.⟦op⟧ add           = simplef[ nat.add  , conjunct ] C.∘ binary
BaseInterp .Model.⟦op⟧ mult          = simplef[ nat.mult , conjunct ] C.∘ binary
BaseInterp .Model.⟦op⟧ (lbl l)       = simplef[ constₛ _ l , 𝒞.id _ ]
BaseInterp .Model.⟦rel⟧ equal-label  = predicate Lbl.equal-label C.∘ binary

open Interpretation BaseInterp public
