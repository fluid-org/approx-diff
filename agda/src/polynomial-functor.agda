{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; suc; lift)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_; tt)
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts)
open import prop-setoid as PS
  using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_)
import fam

module polynomial-functor where

------------------------------------------------------------------------------
-- Syntactic polynomial expressions in one variable, with constants drawn from obj 𝒞,
-- and corresponding functors.
data Poly {o m e} (𝒞 : Category o m e) : Set o where
  one  : Poly 𝒞                              -- constant terminal
  const : Category.obj 𝒞 → Poly 𝒞            -- constant object
  var  : Poly 𝒞                              -- recursive slot
  _[+]_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞          -- sum
  _[×]_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞          -- product

module Sem {o m e} {𝒞 : Category o m e}
           (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (CP : HasCoproducts 𝒞) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  open HasCoproducts CP

  poly-obj : Poly 𝒞 → obj → obj
  poly-obj one         _ = terminal
  poly-obj (const A)   _ = A
  poly-obj var         x = x
  poly-obj (P [+] Q)   x = coprod (poly-obj P x) (poly-obj Q x)
  poly-obj (P [×] Q)   x = prod   (poly-obj P x) (poly-obj Q x)

  record HasMu (Q : Poly 𝒞) : Set (o ⊔ m ⊔ e) where
    field
      μ    : obj
      inF  : poly-obj Q μ ⇒ μ
      ⦅_⦆  : ∀ {y} → (poly-obj Q y ⇒ y) → μ ⇒ y
    -- FIXME: equations (β/η for inF / ⦅_⦆)

------------------------------------------------------------------------------
-- Idx-side projection of a Poly: parameter slots hold setoids rather than
-- full Fam-objects. WIdx-of P P' "applies P' to the carrier W P", embedding
-- the recursive position as W P. Equality is structural recursion on the
-- polynomial.
module _ {o e} where
  open import Data.Sum using (_⊎_)
  open import Data.Product using (_×_)
  open import prop using (_∧_; ⊤; ⊥)

  data IdxPoly : Set (suc (o ⊔ e)) where
    one  : IdxPoly
    param : Setoid o e → IdxPoly
    var  : IdxPoly
    _+ᵖ_  : IdxPoly → IdxPoly → IdxPoly
    _×ᵖ_  : IdxPoly → IdxPoly → IdxPoly

  -- Well-founded tree carrier (Martin-Löf W-types).
  mutual
    data W (P : IdxPoly) : Set o where
      inF : WIdx-of P P → W P

    WIdx-of : IdxPoly → IdxPoly → Set o
    WIdx-of P one         = Level.Lift o 𝟙S
    WIdx-of P (param A)   = Setoid.Carrier A
    WIdx-of P var         = W P
    WIdx-of P (Q₁ +ᵖ Q₂)   = WIdx-of P Q₁ ⊎ WIdx-of P Q₂
    WIdx-of P (Q₁ ×ᵖ Q₂)   = WIdx-of P Q₁ × WIdx-of P Q₂

  mutual
    W-≈ : (P : IdxPoly) → W P → W P → Prop e
    W-≈ P (inF i₁) (inF i₂) = WIdx-≈-of P P i₁ i₂

    WIdx-≈-of : (P Q : IdxPoly) → WIdx-of P Q → WIdx-of P Q → Prop e
    WIdx-≈-of P one         _          _          = ⊤
    WIdx-≈-of P (param A)   x          y          = Setoid._≈_ A x y
    WIdx-≈-of P var         w₁         w₂         = W-≈ P w₁ w₂
    WIdx-≈-of P (Q₁ +ᵖ Q₂)   (inj₁ x₁)  (inj₁ x₂)  = WIdx-≈-of P Q₁ x₁ x₂
    WIdx-≈-of P (Q₁ +ᵖ Q₂)   (inj₁ _)   (inj₂ _)   = ⊥
    WIdx-≈-of P (Q₁ +ᵖ Q₂)   (inj₂ _)   (inj₁ _)   = ⊥
    WIdx-≈-of P (Q₁ +ᵖ Q₂)   (inj₂ y₁)  (inj₂ y₂)  = WIdx-≈-of P Q₂ y₁ y₂
    WIdx-≈-of P (Q₁ ×ᵖ Q₂)   (x₁ , y₁)  (x₂ , y₂)  = WIdx-≈-of P Q₁ x₁ x₂ ∧ WIdx-≈-of P Q₂ y₁ y₂

  mutual
    W-≈-refl : ∀ P {w} → W-≈ P w w
    W-≈-refl P {inF i} = WIdx-≈-of-refl P P {i}

    WIdx-≈-of-refl : ∀ P Q {x} → WIdx-≈-of P Q x x
    WIdx-≈-of-refl P one          = tt
    WIdx-≈-of-refl P (param A) {x} = IsEquivalence.refl (Setoid.isEquivalence A) {x}
    WIdx-≈-of-refl P var      {w}  = W-≈-refl P {w}
    WIdx-≈-of-refl P (Q₁ +ᵖ Q₂) {inj₁ x} = WIdx-≈-of-refl P Q₁ {x}
    WIdx-≈-of-refl P (Q₁ +ᵖ Q₂) {inj₂ y} = WIdx-≈-of-refl P Q₂ {y}
    WIdx-≈-of-refl P (Q₁ ×ᵖ Q₂) {x , y}  = WIdx-≈-of-refl P Q₁ {x} , WIdx-≈-of-refl P Q₂ {y}

  mutual
    W-≈-sym : ∀ P {w₁ w₂} → W-≈ P w₁ w₂ → W-≈ P w₂ w₁
    W-≈-sym P {inF i₁} {inF i₂} eq = WIdx-≈-of-sym P P {i₁} {i₂} eq

    WIdx-≈-of-sym : ∀ P Q {x y} → WIdx-≈-of P Q x y → WIdx-≈-of P Q y x
    WIdx-≈-of-sym P one         _  = tt
    WIdx-≈-of-sym P (param A) {x} {y} eq = IsEquivalence.sym (Setoid.isEquivalence A) eq
    WIdx-≈-of-sym P var       {w₁} {w₂} eq = W-≈-sym P {w₁} {w₂} eq
    WIdx-≈-of-sym P (Q₁ +ᵖ Q₂) {inj₁ x₁} {inj₁ x₂} eq = WIdx-≈-of-sym P Q₁ eq
    WIdx-≈-of-sym P (Q₁ +ᵖ Q₂) {inj₂ y₁} {inj₂ y₂} eq = WIdx-≈-of-sym P Q₂ eq
    WIdx-≈-of-sym P (Q₁ ×ᵖ Q₂) {x₁ , y₁} {x₂ , y₂} (e₁ , e₂) = WIdx-≈-of-sym P Q₁ e₁ , WIdx-≈-of-sym P Q₂ e₂

  mutual
    W-≈-trans : ∀ P {w₁ w₂ w₃} → W-≈ P w₁ w₂ → W-≈ P w₂ w₃ → W-≈ P w₁ w₃
    W-≈-trans P {inF _} {inF _} {inF _} e₁ e₂ = WIdx-≈-of-trans P P e₁ e₂

    WIdx-≈-of-trans : ∀ P Q {x y z} →
                      WIdx-≈-of P Q x y → WIdx-≈-of P Q y z → WIdx-≈-of P Q x z
    WIdx-≈-of-trans P one        _  _  = tt
    WIdx-≈-of-trans P (param A) {x} {y} {z} e₁ e₂ = IsEquivalence.trans (Setoid.isEquivalence A) e₁ e₂
    WIdx-≈-of-trans P var       {x} {y} {z} e₁ e₂ = W-≈-trans P {x} {y} {z} e₁ e₂
    WIdx-≈-of-trans P (Q₁ +ᵖ Q₂) {inj₁ _} {inj₁ _} {inj₁ _} e₁ e₂ = WIdx-≈-of-trans P Q₁ e₁ e₂
    WIdx-≈-of-trans P (Q₁ +ᵖ Q₂) {inj₂ _} {inj₂ _} {inj₂ _} e₁ e₂ = WIdx-≈-of-trans P Q₂ e₁ e₂
    WIdx-≈-of-trans P (Q₁ ×ᵖ Q₂) {_ , _} {_ , _} {_ , _} (e₁ , f₁) (e₂ , f₂) =
      WIdx-≈-of-trans P Q₁ e₁ e₂ , WIdx-≈-of-trans P Q₂ f₁ f₂

  WSetoid : IdxPoly → Setoid o e
  WSetoid P = record
    { Carrier = W P
    ; _≈_ = W-≈ P
    ; isEquivalence = record
      { refl = λ {w} → W-≈-refl P {w}
      ; sym = λ {w₁} {w₂} → W-≈-sym P {w₁} {w₂}
      ; trans = λ {w₁} {w₂} {w₃} → W-≈-trans P {w₁} {w₂} {w₃}
      }
    }

------------------------------------------------------------------------------
-- HasMu instance for the Fam category.
module WFam {o m e} (os es : _) {𝒞 : Category o m e}
            (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where
  open Category 𝒞
  open IsEquivalence
  open HasTerminal
  open HasProducts P
  open fam.CategoryOfFamilies os es 𝒞
  open products P  -- Fam-level products
  open _⇒f_
  open Sem (terminal T) products coproducts

  ----------------------------------------------------------------------
  -- Generic μ-types in Fam(𝒞), for polynomials Q : Poly cat. The idx side is WSetoid of Q (projecting param
  -- slots from Fam-objs to their idx setoids); the fibre side is built recursively over Q using 𝒞's products.
  module W-types (Q : Poly cat) where
    open Obj
    open Mor
    open Fam

    idx-of : Poly cat → IdxPoly
    idx-of Poly.one        = one
    idx-of (Poly.const A)  = param (A .idx)
    idx-of Poly.var        = var
    idx-of (P Poly.[+] Q)  = idx-of P +ᵖ idx-of Q
    idx-of (P Poly.[×] Q)  = idx-of P ×ᵖ idx-of Q

    poly : IdxPoly
    poly = idx-of Q

    WFam-of-fm : (P : Poly cat) → WIdx-of poly (idx-of P) → obj
    WFam-of-fm Poly.one        _        = T .witness
    WFam-of-fm (Poly.const A)  a        = A .fam .fm a
    WFam-of-fm Poly.var        (inF i)  = WFam-of-fm Q i
    WFam-of-fm (P Poly.[+] Q)  (inj₁ x) = WFam-of-fm P x
    WFam-of-fm (P Poly.[+] Q)  (inj₂ y) = WFam-of-fm Q y
    WFam-of-fm (P Poly.[×] Q)  (x , y)  = prod (WFam-of-fm P x) (WFam-of-fm Q y)

    WFam-of-subst : (P : Poly cat) → ∀ {x y} → WIdx-≈-of poly (idx-of P) x y → WFam-of-fm P x ⇒ WFam-of-fm P y
    WFam-of-subst Poly.one _ = id _
    WFam-of-subst (Poly.const A) {x} {y} eq = A .fam .subst eq
    WFam-of-subst Poly.var {inF i₁} {inF i₂} eq = WFam-of-subst Q eq
    WFam-of-subst (P Poly.[+] Q) {inj₁ _} {inj₁ _} eq = WFam-of-subst P eq
    WFam-of-subst (P Poly.[+] Q) {inj₂ _} {inj₂ _} eq = WFam-of-subst Q eq
    WFam-of-subst (P Poly.[+] Q) {inj₁ _} {inj₂ _} ()
    WFam-of-subst (P Poly.[+] Q) {inj₂ _} {inj₁ _} ()
    WFam-of-subst (P Poly.[×] Q) {_ , _} {_ , _} (e₁ , e₂) =
      prod-m (WFam-of-subst P e₁) (WFam-of-subst Q e₂)

    WFam-of-refl* : (P : Poly cat) → ∀ {x} →
                    WFam-of-subst P (WIdx-≈-of-refl poly (idx-of P) {x}) ≈ id _
    WFam-of-refl* Poly.one         = isEquiv .refl
    WFam-of-refl* (Poly.const A) {x} = A .fam .refl*
    WFam-of-refl* Poly.var {inF i} = WFam-of-refl* Q {i}
    WFam-of-refl* (P Poly.[+] Q) {inj₁ x} = WFam-of-refl* P {x}
    WFam-of-refl* (P Poly.[+] Q) {inj₂ y} = WFam-of-refl* Q {y}
    WFam-of-refl* (P Poly.[×] Q) {x , y}  =
      begin
        prod-m (WFam-of-subst P _) (WFam-of-subst Q _)
      ≈⟨ prod-m-cong (WFam-of-refl* P {x}) (WFam-of-refl* Q {y}) ⟩
        prod-m (id _) (id _)
      ≈⟨ prod-m-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv

    WFam-of-trans* : (P : Poly cat) → ∀ {x y z}
                     (e₁ : WIdx-≈-of poly (idx-of P) y z) (e₂ : WIdx-≈-of poly (idx-of P) x y) →
                     WFam-of-subst P (WIdx-≈-of-trans poly (idx-of P) e₂ e₁) ≈
                     (WFam-of-subst P e₁ ∘ WFam-of-subst P e₂)
    WFam-of-trans* Poly.one _ _ = isEquiv .sym id-left
    WFam-of-trans* (Poly.const A) e₁ e₂ = A .fam .trans* e₁ e₂
    WFam-of-trans* Poly.var {inF _} {inF _} {inF _} e₁ e₂ =
      WFam-of-trans* Q e₁ e₂
    WFam-of-trans* (P Poly.[+] Q) {inj₁ _} {inj₁ _} {inj₁ _} e₁ e₂ = WFam-of-trans* P e₁ e₂
    WFam-of-trans* (P Poly.[+] Q) {inj₂ _} {inj₂ _} {inj₂ _} e₁ e₂ = WFam-of-trans* Q e₁ e₂
    WFam-of-trans* (P Poly.[×] Q) {_ , _} {_ , _} {_ , _} (e₁ , f₁) (e₂ , f₂) =
      begin
        prod-m (WFam-of-subst P _) (WFam-of-subst Q _)
      ≈⟨ prod-m-cong (WFam-of-trans* P e₁ e₂) (WFam-of-trans* Q f₁ f₂) ⟩
        prod-m (WFam-of-subst P e₁ ∘ WFam-of-subst P e₂) (WFam-of-subst Q f₁ ∘ WFam-of-subst Q f₂)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-of-subst P e₁) (WFam-of-subst Q f₁) ∘ prod-m (WFam-of-subst P e₂) (WFam-of-subst Q f₂)
      ∎ where open ≈-Reasoning isEquiv

    WFam : Fam (WSetoid poly) 𝒞
    WFam .fm (inF i)                            = WFam-of-fm Q i
    WFam .subst {inF _} {inF _} eq              = WFam-of-subst Q eq
    WFam .refl* {inF _}                         = WFam-of-refl* Q
    WFam .trans* {inF _} {inF _} {inF _} e₁ e₂  = WFam-of-trans* Q e₁ e₂

    WObj : Obj
    WObj .idx = WSetoid poly
    WObj .fam = WFam

    embed-idx : (P : Poly cat) → poly-obj P WObj .idx .Setoid.Carrier → WIdx-of poly (idx-of P)
    embed-idx Poly.one         (lift tt)  = lift tt
    embed-idx (Poly.const A)   a          = a
    embed-idx Poly.var         w          = w
    embed-idx (P Poly.[+] Q)   (inj₁ x)   = inj₁ (embed-idx P x)
    embed-idx (P Poly.[+] Q)   (inj₂ y)   = inj₂ (embed-idx Q y)
    embed-idx (P Poly.[×] Q)   (x , y)    = (embed-idx P x , embed-idx Q y)

    embed-≈ : (P : Poly cat) → ∀ {x y} →
              poly-obj P WObj .idx .Setoid._≈_ x y → WIdx-≈-of poly (idx-of P) (embed-idx P x) (embed-idx P y)
    embed-≈ Poly.one         _   = tt
    embed-≈ (Poly.const A)   eq  = eq
    embed-≈ Poly.var         eq  = eq
    embed-≈ (P Poly.[+] Q) {inj₁ _} {inj₁ _} eq        = embed-≈ P eq
    embed-≈ (P Poly.[+] Q) {inj₂ _} {inj₂ _} eq        = embed-≈ Q eq
    embed-≈ (P Poly.[×] Q) {_ , _} {_ , _} (e₁ , e₂)   = (embed-≈ P e₁ , embed-≈ Q e₂)

    embed-fam : (P : Poly cat) (i : poly-obj P WObj .idx .Setoid.Carrier) →
                poly-obj P WObj .fam .fm i ⇒ WFam-of-fm P (embed-idx P i)
    embed-fam Poly.one       (lift tt)  = id _
    embed-fam (Poly.const A) a          = id _
    embed-fam Poly.var       (inF _)    = id _
    embed-fam (P Poly.[+] Q) (inj₁ x)   = embed-fam P x
    embed-fam (P Poly.[+] Q) (inj₂ y)   = embed-fam Q y
    embed-fam (P Poly.[×] Q) (x , y)    = prod-m (embed-fam P x) (embed-fam Q y)

    embed-fam-natural : (P : Poly cat) → ∀ {x₁ x₂} (e : poly-obj P WObj .idx .Setoid._≈_ x₁ x₂) →
                        (embed-fam P x₂ ∘ poly-obj P WObj .fam .subst e) ≈
                        (WFam-of-subst P (embed-≈ P e) ∘ embed-fam P x₁)
    embed-fam-natural Poly.one _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (Poly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural Poly.var {inF _} {inF _} _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (P Poly.[+] Q) {inj₁ _} {inj₁ _} e = embed-fam-natural P e
    embed-fam-natural (P Poly.[+] Q) {inj₂ _} {inj₂ _} e = embed-fam-natural Q e
    embed-fam-natural (P Poly.[×] Q) {x₁ , y₁} {x₂ , y₂} (e , f) =
      begin
        prod-m (embed-fam P x₂) (embed-fam Q y₂) ∘ prod-m _ _
      ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
        prod-m (embed-fam P x₂ ∘ _) (embed-fam Q y₂ ∘ _)
      ≈⟨ prod-m-cong (embed-fam-natural P e) (embed-fam-natural Q f) ⟩
        prod-m (WFam-of-subst P (embed-≈ P e) ∘ embed-fam P x₁) (WFam-of-subst Q (embed-≈ Q f) ∘ embed-fam Q y₁)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-of-subst P (embed-≈ P e)) (WFam-of-subst Q (embed-≈ Q f)) ∘ prod-m (embed-fam P x₁) (embed-fam Q y₁)
      ∎ where open ≈-Reasoning isEquiv

    sup : Mor (poly-obj Q WObj) WObj
    sup .idxf .PS._⇒_.func i          = inF (embed-idx Q i)
    sup .idxf .PS._⇒_.func-resp-≈ eq  = embed-≈ Q eq
    sup .famf .transf i               = embed-fam Q i
    sup .famf .natural e              = embed-fam-natural Q e

    module _ {y : Obj} (alg : Mor (poly-obj Q y) y) where

      project-idx : (P : Poly cat) → WIdx-of poly (idx-of P) → poly-obj P y .idx .Setoid.Carrier
      project-idx Poly.one _                       = lift tt
      project-idx (Poly.const A) a                 = a
      project-idx Poly.var (inF i)              = alg .idxf .PS._⇒_.func (project-idx Q i)
      project-idx (P Poly.[+] Q) (inj₁ x)          = inj₁ (project-idx P x)
      project-idx (P Poly.[+] Q) (inj₂ z)          = inj₂ (project-idx Q z)
      project-idx (P Poly.[×] Q) (x , z)           = (project-idx P x , project-idx Q z)

      project-≈ : (P : Poly cat) → ∀ {x z} → WIdx-≈-of poly (idx-of P) x z →
                  poly-obj P y .idx .Setoid._≈_ (project-idx P x) (project-idx P z)
      project-≈ Poly.one _ = tt
      project-≈ (Poly.const A) eq = eq
      project-≈ Poly.var {inF _} {inF _} eq =
        alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)
      project-≈ (P Poly.[+] Q) {inj₁ _} {inj₁ _} eq = project-≈ P eq
      project-≈ (P Poly.[+] Q) {inj₂ _} {inj₂ _} eq = project-≈ Q eq
      project-≈ (P Poly.[×] Q) {_ , _} {_ , _} (e , f) = (project-≈ P e , project-≈ Q f)

      project-fam : (P : Poly cat) (i : WIdx-of poly (idx-of P)) →
                    WFam-of-fm P i ⇒ poly-obj P y .fam .fm (project-idx P i)
      project-fam Poly.one _                       = id _
      project-fam (Poly.const A) a                 = id _
      project-fam Poly.var (inF i)              =
        alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      project-fam (P Poly.[+] Q) (inj₁ x)          = project-fam P x
      project-fam (P Poly.[+] Q) (inj₂ z)          = project-fam Q z
      project-fam (P Poly.[×] Q) (x , z)           =
        prod-m (project-fam P x) (project-fam Q z)

      project-fam-natural : (P : Poly cat) → ∀ {x z} (e : WIdx-≈-of poly (idx-of P) x z) →
                            (project-fam P z ∘ WFam-of-subst P e) ≈
                            (poly-obj P y .fam .subst (project-≈ P e) ∘ project-fam P x)
      project-fam-natural Poly.one _ =
        isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural (Poly.const A) _ =
        isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural Poly.var {inF i₁} {inF i₂} eq =
        begin
          (alg .famf .transf (project-idx Q i₂) ∘ project-fam Q i₂) ∘ WFam-of-subst Q eq
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (project-idx Q i₂) ∘ (project-fam Q i₂ ∘ WFam-of-subst Q eq)
        ≈⟨ ∘-cong (isEquiv .refl) (project-fam-natural Q eq) ⟩
          alg .famf .transf (project-idx Q i₂) ∘
            (poly-obj Q y .fam .subst (project-≈ Q eq) ∘ project-fam Q i₁)
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (project-idx Q i₂) ∘
            poly-obj Q y .fam .subst (project-≈ Q eq)) ∘ project-fam Q i₁
        ≈⟨ ∘-cong (alg .famf .natural (project-≈ Q eq)) (isEquiv .refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)) ∘ alg .famf .transf (project-idx Q i₁)) ∘ project-fam Q i₁
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)) ∘
            (alg .famf .transf (project-idx Q i₁) ∘ project-fam Q i₁)
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural (P Poly.[+] Q) {inj₁ _} {inj₁ _} e = project-fam-natural P e
      project-fam-natural (P Poly.[+] Q) {inj₂ _} {inj₂ _} e = project-fam-natural Q e
      project-fam-natural (P Poly.[×] Q) {x₁ , z₁} {x₂ , z₂} (e , f) =
        begin
          prod-m (project-fam P x₂) (project-fam Q z₂) ∘ prod-m _ _
        ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
          prod-m (project-fam P x₂ ∘ _) (project-fam Q z₂ ∘ _)
        ≈⟨ prod-m-cong (project-fam-natural P e) (project-fam-natural Q f) ⟩
          prod-m (_ ∘ project-fam P x₁) (_ ∘ project-fam Q z₁)
        ≈⟨ pair-functorial _ _ _ _ ⟩
          prod-m _ _ ∘ prod-m (project-fam P x₁) (project-fam Q z₁)
        ∎ where open ≈-Reasoning isEquiv

      fold-mor : Mor WObj y
      fold-mor .idxf .PS._⇒_.func (inF i)                   = alg .idxf .PS._⇒_.func (project-idx Q i)
      fold-mor .idxf .PS._⇒_.func-resp-≈ {inF _} {inF _} eq = alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)
      fold-mor .famf .transf (inF i)                        = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      fold-mor .famf .natural {inF _} {inF _} eq            = project-fam-natural Poly.var eq

    fold : ∀ {y : Obj} → Mor (poly-obj Q y) y → Mor WObj y
    fold alg = fold-mor alg

  hasMu : (Q : Poly cat) → HasMu Q
  hasMu Q .HasMu.μ = W-types.WObj Q
  hasMu Q .HasMu.inF = W-types.sup Q
  hasMu Q .HasMu.⦅_⦆ = W-types.fold Q
