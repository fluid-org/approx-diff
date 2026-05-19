{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; suc; lift)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_; tt)
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; cong₂)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasExponentials; IsStrongMonad; StrongMonad)
open import cmon-enriched using (CMonEnriched)
open import prop-setoid as PS
  using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_)
import fam

module polynomial-functor where

------------------------------------------------------------------------------
-- Syntactic polynomial expressions in one variable, with constants drawn from obj 𝒞; they form a category.
data Poly {o m e} (𝒞 : Category o m e) : Set o where
  one  : Poly 𝒞                              -- constant terminal
  const : Category.obj 𝒞 → Poly 𝒞            -- constant object
  var  : Poly 𝒞                              -- recursive slot
  _+_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞          -- sum
  _×_  : Poly 𝒞 → Poly 𝒞 → Poly 𝒞          -- product

_∘ₚ_ : ∀ {o m e} {𝒞 : Category o m e} → Poly 𝒞 → Poly 𝒞 → Poly 𝒞
one        ∘ₚ Q = one
const A    ∘ₚ Q = const A
var        ∘ₚ Q = Q
(P₁ + P₂)  ∘ₚ Q = (P₁ ∘ₚ Q) + (P₂ ∘ₚ Q)
(P₁ × P₂)  ∘ₚ Q = (P₁ ∘ₚ Q) × (P₂ ∘ₚ Q)

module Sem {o m e} {𝒞 : Category o m e}
           (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (CP : HasCoproducts 𝒞) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  open HasCoproducts CP
  open IsStrongMonad public

  poly-obj : Poly 𝒞 → obj → obj
  poly-obj one         _ = terminal
  poly-obj (const A)   _ = A
  poly-obj var         x = x
  poly-obj (P + Q)     x = coprod (poly-obj P x) (poly-obj Q x)
  poly-obj (P × Q)     x = prod   (poly-obj P x) (poly-obj Q x)

  -- Polynomial composition agrees with composition of functor actions.
  poly-obj-comp : ∀ P Q X → poly-obj (P ∘ₚ Q) X ≡ poly-obj P (poly-obj Q X)
  poly-obj-comp one        Q X = ≡.refl
  poly-obj-comp (const A)  Q X = ≡.refl
  poly-obj-comp var        Q X = ≡.refl
  poly-obj-comp (P₁ + P₂)  Q X = cong₂ coprod (poly-obj-comp P₁ Q X) (poly-obj-comp P₂ Q X)
  poly-obj-comp (P₁ × P₂)  Q X = cong₂ prod   (poly-obj-comp P₁ Q X) (poly-obj-comp P₂ Q X)

  record HasMu : Set (o ⊔ m ⊔ e) where
    field
      μ    : Poly 𝒞 → obj
      inF  : ∀ Q → poly-obj Q (μ Q) ⇒ μ Q
      ⦅_⦆  : ∀ {Q y} → (poly-obj Q y ⇒ y) → μ Q ⇒ y
    -- FIXME: equations (β/η for inF / ⦅_⦆)

  -- Strong monad whose endofunctor is polynomial.
  record PolyMonad : Set (o ⊔ m ⊔ e) where
    field
      P-Mon       : Poly 𝒞
      isStrongMon : IsStrongMonad P (poly-obj P-Mon)
    open IsStrongMonad isStrongMon public
  open PolyMonad

  asStrongMonad : PolyMonad → StrongMonad 𝒞 P
  asStrongMonad pm .StrongMonad.M           = poly-obj (pm .P-Mon)
  asStrongMonad pm .StrongMonad.isStrongMon = pm .isStrongMon

  PolyMonad-Id : PolyMonad
  PolyMonad-Id .P-Mon                  = var
  PolyMonad-Id .isStrongMon .unit {x}  = id x
  PolyMonad-Id .isStrongMon .extend f  = f

  -- Strong monad augmented with a force (retraction of unit), giving every object a Mon-algebra.
  record PointedMonad : Set (o ⊔ m ⊔ e) where
    field
      polyMonad : PolyMonad
      force     : ∀ {x} → poly-obj (polyMonad .P-Mon) x ⇒ x
    open PolyMonad polyMonad public
    -- FIXME: force ∘ unit ≈ id; force ∘ mul ≈ force ∘ map force
  open PointedMonad

  PointedMonad-Id : PointedMonad
  PointedMonad-Id .polyMonad = PolyMonad-Id
  PointedMonad-Id .force {x} = id x

  -- Lifting monad L X = terminal + X, with force propagating "bottom" via the zero morphism available in a
  -- CMon-enriched category.
  module _ (E : HasExponentials 𝒞 P) (CME : CMonEnriched 𝒞) where
    open HasExponentials E
    open CMonEnriched CME using (εm)

    PointedMonad-L : PointedMonad
    PointedMonad-L .polyMonad .P-Mon                    = one + var
    PointedMonad-L .polyMonad .isStrongMon .unit        = in₂
    PointedMonad-L .polyMonad .isStrongMon .extend f    =
      eval ∘ pair (copair (lambda (in₁ ∘ p₁)) (lambda (f ∘ pair p₂ p₁)) ∘ p₂) p₁
    PointedMonad-L .force                               = copair εm (id _)

------------------------------------------------------------------------------
-- Like Poly above but constant slots hold a setoid rather than a category object. Used to build the W-type
-- carrier of HasMu in the Fam category. W P is the set of P-shaped trees; W-≈ is tree equality by structural
-- recursion on the polynomial.
module _ {o e} where
  open import Data.Sum using (_⊎_)
  open import Data.Product using () renaming (_×_ to _×T_)
  open import prop using (_∧_; ⊤; ⊥)

  data IdxPoly : Set (suc (o ⊔ e)) where
    one  : IdxPoly
    param : Setoid o e → IdxPoly
    var  : IdxPoly
    _+_  : IdxPoly → IdxPoly → IdxPoly
    _×_  : IdxPoly → IdxPoly → IdxPoly

  -- Well-founded tree carrier (Martin-Löf W-types).
  mutual
    data W (P : IdxPoly) : Set o where
      inF : WIdx P P → W P

    WIdx : IdxPoly → IdxPoly → Set o
    WIdx P one         = Level.Lift o 𝟙S
    WIdx P (param A)   = Setoid.Carrier A
    WIdx P var         = W P
    WIdx P (Q₁ + Q₂)   = WIdx P Q₁ ⊎ WIdx P Q₂
    WIdx P (Q₁ × Q₂)   = WIdx P Q₁ ×T WIdx P Q₂

  mutual
    W-≈ : (P : IdxPoly) → W P → W P → Prop e
    W-≈ P (inF i₁) (inF i₂) = WIdx-≈ P P i₁ i₂

    WIdx-≈ : (P Q : IdxPoly) → WIdx P Q → WIdx P Q → Prop e
    WIdx-≈ P one         _          _          = ⊤
    WIdx-≈ P (param A)   x          y          = Setoid._≈_ A x y
    WIdx-≈ P var         w₁         w₂         = W-≈ P w₁ w₂
    WIdx-≈ P (Q₁ + Q₂)   (inj₁ x₁)  (inj₁ x₂)  = WIdx-≈ P Q₁ x₁ x₂
    WIdx-≈ P (Q₁ + Q₂)   (inj₁ _)   (inj₂ _)   = ⊥
    WIdx-≈ P (Q₁ + Q₂)   (inj₂ _)   (inj₁ _)   = ⊥
    WIdx-≈ P (Q₁ + Q₂)   (inj₂ y₁)  (inj₂ y₂)  = WIdx-≈ P Q₂ y₁ y₂
    WIdx-≈ P (Q₁ × Q₂)   (x₁ , y₁)  (x₂ , y₂)  = WIdx-≈ P Q₁ x₁ x₂ ∧ WIdx-≈ P Q₂ y₁ y₂

  mutual
    W-≈-refl : ∀ P {w} → W-≈ P w w
    W-≈-refl P {inF i} = WIdx-≈-refl P P {i}

    WIdx-≈-refl : ∀ P Q {x} → WIdx-≈ P Q x x
    WIdx-≈-refl P one                   = tt
    WIdx-≈-refl P (param A) {x}         = IsEquivalence.refl (Setoid.isEquivalence A) {x}
    WIdx-≈-refl P var       {w}         = W-≈-refl P {w}
    WIdx-≈-refl P (Q₁ + Q₂) {inj₁ x}    = WIdx-≈-refl P Q₁ {x}
    WIdx-≈-refl P (Q₁ + Q₂) {inj₂ y}    = WIdx-≈-refl P Q₂ {y}
    WIdx-≈-refl P (Q₁ × Q₂) {x , y}     = WIdx-≈-refl P Q₁ {x} , WIdx-≈-refl P Q₂ {y}

  mutual
    W-≈-sym : ∀ P {w₁ w₂} → W-≈ P w₁ w₂ → W-≈ P w₂ w₁
    W-≈-sym P {inF i₁} {inF i₂} eq = WIdx-≈-sym P P {i₁} {i₂} eq

    WIdx-≈-sym : ∀ P Q {x y} → WIdx-≈ P Q x y → WIdx-≈ P Q y x
    WIdx-≈-sym P one         _  = tt
    WIdx-≈-sym P (param A) {x} {y} eq = IsEquivalence.sym (Setoid.isEquivalence A) eq
    WIdx-≈-sym P var       {w₁} {w₂} eq = W-≈-sym P {w₁} {w₂} eq
    WIdx-≈-sym P (Q₁ + Q₂) {inj₁ x₁} {inj₁ x₂} eq = WIdx-≈-sym P Q₁ eq
    WIdx-≈-sym P (Q₁ + Q₂) {inj₂ y₁} {inj₂ y₂} eq = WIdx-≈-sym P Q₂ eq
    WIdx-≈-sym P (Q₁ × Q₂) {x₁ , y₁} {x₂ , y₂} (e₁ , e₂) = WIdx-≈-sym P Q₁ e₁ , WIdx-≈-sym P Q₂ e₂

  mutual
    W-≈-trans : ∀ P {w₁ w₂ w₃} → W-≈ P w₁ w₂ → W-≈ P w₂ w₃ → W-≈ P w₁ w₃
    W-≈-trans P {inF _} {inF _} {inF _} e₁ e₂ = WIdx-≈-trans P P e₁ e₂

    WIdx-≈-trans : ∀ P Q {x y z} →
                      WIdx-≈ P Q x y → WIdx-≈ P Q y z → WIdx-≈ P Q x z
    WIdx-≈-trans P one        _  _  = tt
    WIdx-≈-trans P (param A) {x} {y} {z} e₁ e₂ = IsEquivalence.trans (Setoid.isEquivalence A) e₁ e₂
    WIdx-≈-trans P var       {x} {y} {z} e₁ e₂ = W-≈-trans P {x} {y} {z} e₁ e₂
    WIdx-≈-trans P (Q₁ + Q₂) {inj₁ _} {inj₁ _} {inj₁ _} e₁ e₂ = WIdx-≈-trans P Q₁ e₁ e₂
    WIdx-≈-trans P (Q₁ + Q₂) {inj₂ _} {inj₂ _} {inj₂ _} e₁ e₂ = WIdx-≈-trans P Q₂ e₁ e₂
    WIdx-≈-trans P (Q₁ × Q₂) {_ , _} {_ , _} {_ , _} (e₁ , f₁) (e₂ , f₂) =
      WIdx-≈-trans P Q₁ e₁ e₂ , WIdx-≈-trans P Q₂ f₁ f₂

  WSetoid : IdxPoly → Setoid o e
  WSetoid P .Setoid.Carrier                            = W P
  WSetoid P .Setoid._≈_                                = W-≈ P
  WSetoid P .Setoid.isEquivalence .IsEquivalence.refl  {w} = W-≈-refl P {w}
  WSetoid P .Setoid.isEquivalence .IsEquivalence.sym   {w₁} {w₂} = W-≈-sym P {w₁} {w₂}
  WSetoid P .Setoid.isEquivalence .IsEquivalence.trans {w₁} {w₂} {w₃} = W-≈-trans P {w₁} {w₂} {w₃}

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction.
module WFam {o m e} (os es : _) {𝒞 : Category o m e} (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where
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
    idx-of (P Poly.+ Q)  = idx-of P + idx-of Q
    idx-of (P Poly.× Q)  = idx-of P × idx-of Q

    poly : IdxPoly
    poly = idx-of Q

    WFam-fm : (P : Poly cat) → WIdx poly (idx-of P) → obj
    WFam-fm Poly.one          _        = T .witness
    WFam-fm (Poly.const A)    a        = A .fam .fm a
    WFam-fm Poly.var          (inF i)  = WFam-fm Q i
    WFam-fm (P Poly.+ Q)      (inj₁ x) = WFam-fm P x
    WFam-fm (P Poly.+ Q)      (inj₂ y) = WFam-fm Q y
    WFam-fm (P Poly.× Q)      (x , y)  = prod (WFam-fm P x) (WFam-fm Q y)

    WFam-subst : (P : Poly cat) → ∀ {x y} → WIdx-≈ poly (idx-of P) x y → WFam-fm P x ⇒ WFam-fm P y
    WFam-subst Poly.one _ = id _
    WFam-subst (Poly.const A) {x} {y} eq = A .fam .subst eq
    WFam-subst Poly.var {inF i₁} {inF i₂} eq = WFam-subst Q eq
    WFam-subst (P Poly.+ Q) {inj₁ _} {inj₁ _} eq = WFam-subst P eq
    WFam-subst (P Poly.+ Q) {inj₂ _} {inj₂ _} eq = WFam-subst Q eq
    WFam-subst (P Poly.+ Q) {inj₁ _} {inj₂ _} ()
    WFam-subst (P Poly.+ Q) {inj₂ _} {inj₁ _} ()
    WFam-subst (P Poly.× Q) {_ , _} {_ , _} (e₁ , e₂) =
      prod-m (WFam-subst P e₁) (WFam-subst Q e₂)

    WFam-refl* : (P : Poly cat) → ∀ {x} →
                    WFam-subst P (WIdx-≈-refl poly (idx-of P) {x}) ≈ id _
    WFam-refl* Poly.one         = isEquiv .refl
    WFam-refl* (Poly.const A) {x} = A .fam .refl*
    WFam-refl* Poly.var {inF i} = WFam-refl* Q {i}
    WFam-refl* (P Poly.+ Q) {inj₁ x} = WFam-refl* P {x}
    WFam-refl* (P Poly.+ Q) {inj₂ y} = WFam-refl* Q {y}
    WFam-refl* (P Poly.× Q) {x , y}  =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-refl* P {x}) (WFam-refl* Q {y}) ⟩
        prod-m (id _) (id _)
      ≈⟨ prod-m-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv

    WFam-trans* : (P : Poly cat) → ∀ {x y z}
                     (e₁ : WIdx-≈ poly (idx-of P) y z) (e₂ : WIdx-≈ poly (idx-of P) x y) →
                     WFam-subst P (WIdx-≈-trans poly (idx-of P) e₂ e₁) ≈
                     (WFam-subst P e₁ ∘ WFam-subst P e₂)
    WFam-trans* Poly.one _ _ = isEquiv .sym id-left
    WFam-trans* (Poly.const A) e₁ e₂ = A .fam .trans* e₁ e₂
    WFam-trans* Poly.var {inF _} {inF _} {inF _} e₁ e₂ =
      WFam-trans* Q e₁ e₂
    WFam-trans* (P Poly.+ Q) {inj₁ _} {inj₁ _} {inj₁ _} e₁ e₂ = WFam-trans* P e₁ e₂
    WFam-trans* (P Poly.+ Q) {inj₂ _} {inj₂ _} {inj₂ _} e₁ e₂ = WFam-trans* Q e₁ e₂
    WFam-trans* (P Poly.× Q) {_ , _} {_ , _} {_ , _} (e₁ , f₁) (e₂ , f₂) =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-trans* P e₁ e₂) (WFam-trans* Q f₁ f₂) ⟩
        prod-m (WFam-subst P e₁ ∘ WFam-subst P e₂) (WFam-subst Q f₁ ∘ WFam-subst Q f₂)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P e₁) (WFam-subst Q f₁) ∘ prod-m (WFam-subst P e₂) (WFam-subst Q f₂)
      ∎ where open ≈-Reasoning isEquiv

    WFam : Fam (WSetoid poly) 𝒞
    WFam .fm (inF i)                            = WFam-fm Q i
    WFam .subst {inF _} {inF _} eq              = WFam-subst Q eq
    WFam .refl* {inF _}                         = WFam-refl* Q
    WFam .trans* {inF _} {inF _} {inF _} e₁ e₂  = WFam-trans* Q e₁ e₂

    WObj : Obj
    WObj .idx = WSetoid poly
    WObj .fam = WFam

    embed-idx : (P : Poly cat) → poly-obj P WObj .idx .Setoid.Carrier → WIdx poly (idx-of P)
    embed-idx Poly.one         (lift tt)  = lift tt
    embed-idx (Poly.const A)   a          = a
    embed-idx Poly.var         w          = w
    embed-idx (P Poly.+ Q)     (inj₁ x)   = inj₁ (embed-idx P x)
    embed-idx (P Poly.+ Q)     (inj₂ y)   = inj₂ (embed-idx Q y)
    embed-idx (P Poly.× Q)     (x , y)    = (embed-idx P x , embed-idx Q y)

    embed-≈ : (P : Poly cat) → ∀ {x y} →
              poly-obj P WObj .idx .Setoid._≈_ x y → WIdx-≈ poly (idx-of P) (embed-idx P x) (embed-idx P y)
    embed-≈ Poly.one         _   = tt
    embed-≈ (Poly.const A)   eq  = eq
    embed-≈ Poly.var         eq  = eq
    embed-≈ (P Poly.+ Q) {inj₁ _} {inj₁ _} eq        = embed-≈ P eq
    embed-≈ (P Poly.+ Q) {inj₂ _} {inj₂ _} eq        = embed-≈ Q eq
    embed-≈ (P Poly.× Q) {_ , _} {_ , _} (e₁ , e₂)   = (embed-≈ P e₁ , embed-≈ Q e₂)

    embed-fam : (P : Poly cat) (i : poly-obj P WObj .idx .Setoid.Carrier) →
                poly-obj P WObj .fam .fm i ⇒ WFam-fm P (embed-idx P i)
    embed-fam Poly.one         (lift tt)  = id _
    embed-fam (Poly.const A)   a          = id _
    embed-fam Poly.var         (inF _)    = id _
    embed-fam (P Poly.+ Q)     (inj₁ x)   = embed-fam P x
    embed-fam (P Poly.+ Q)     (inj₂ y)   = embed-fam Q y
    embed-fam (P Poly.× Q)     (x , y)    = prod-m (embed-fam P x) (embed-fam Q y)

    embed-fam-natural : (P : Poly cat) → ∀ {x₁ x₂} (e : poly-obj P WObj .idx .Setoid._≈_ x₁ x₂) →
                        (embed-fam P x₂ ∘ poly-obj P WObj .fam .subst e) ≈
                        (WFam-subst P (embed-≈ P e) ∘ embed-fam P x₁)
    embed-fam-natural Poly.one _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (Poly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural Poly.var {inF _} {inF _} _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (P Poly.+ Q) {inj₁ _} {inj₁ _} e = embed-fam-natural P e
    embed-fam-natural (P Poly.+ Q) {inj₂ _} {inj₂ _} e = embed-fam-natural Q e
    embed-fam-natural (P Poly.× Q) {x₁ , y₁} {x₂ , y₂} (e , f) =
      begin
        prod-m (embed-fam P x₂) (embed-fam Q y₂) ∘ prod-m _ _
      ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
        prod-m (embed-fam P x₂ ∘ _) (embed-fam Q y₂ ∘ _)
      ≈⟨ prod-m-cong (embed-fam-natural P e) (embed-fam-natural Q f) ⟩
        prod-m (WFam-subst P (embed-≈ P e) ∘ embed-fam P x₁) (WFam-subst Q (embed-≈ Q f) ∘ embed-fam Q y₁)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P (embed-≈ P e)) (WFam-subst Q (embed-≈ Q f)) ∘ prod-m (embed-fam P x₁) (embed-fam Q y₁)
      ∎ where open ≈-Reasoning isEquiv

    inF-mor : Mor (poly-obj Q WObj) WObj
    inF-mor .idxf .PS._⇒_.func i          = inF (embed-idx Q i)
    inF-mor .idxf .PS._⇒_.func-resp-≈ eq  = embed-≈ Q eq
    inF-mor .famf .transf i               = embed-fam Q i
    inF-mor .famf .natural e              = embed-fam-natural Q e

    module _ {y : Obj} (alg : Mor (poly-obj Q y) y) where

      project-idx : (P : Poly cat) → WIdx poly (idx-of P) → poly-obj P y .idx .Setoid.Carrier
      project-idx Poly.one       _         = lift tt
      project-idx (Poly.const A) a         = a
      project-idx Poly.var       (inF i)   = alg .idxf .PS._⇒_.func (project-idx Q i)
      project-idx (P Poly.+ Q)   (inj₁ x)  = inj₁ (project-idx P x)
      project-idx (P Poly.+ Q)   (inj₂ z)  = inj₂ (project-idx Q z)
      project-idx (P Poly.× Q)   (x , z)   = (project-idx P x , project-idx Q z)

      project-≈ : (P : Poly cat) → ∀ {x z} → WIdx-≈ poly (idx-of P) x z →
                  poly-obj P y .idx .Setoid._≈_ (project-idx P x) (project-idx P z)
      project-≈ Poly.one _ = tt
      project-≈ (Poly.const A) eq = eq
      project-≈ Poly.var {inF _} {inF _} eq =
        alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)
      project-≈ (P Poly.+ Q) {inj₁ _} {inj₁ _} eq = project-≈ P eq
      project-≈ (P Poly.+ Q) {inj₂ _} {inj₂ _} eq = project-≈ Q eq
      project-≈ (P Poly.× Q) {_ , _} {_ , _} (e , f) = (project-≈ P e , project-≈ Q f)

      project-fam : (P : Poly cat) (i : WIdx poly (idx-of P)) →
                    WFam-fm P i ⇒ poly-obj P y .fam .fm (project-idx P i)
      project-fam Poly.one _            = id _
      project-fam (Poly.const A) a      = id _
      project-fam Poly.var (inF i)      = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      project-fam (P Poly.+ Q) (inj₁ x) = project-fam P x
      project-fam (P Poly.+ Q) (inj₂ z) = project-fam Q z
      project-fam (P Poly.× Q) (x , z)  = prod-m (project-fam P x) (project-fam Q z)

      project-fam-natural : (P : Poly cat) → ∀ {x z} (e : WIdx-≈ poly (idx-of P) x z) →
                            (project-fam P z ∘ WFam-subst P e) ≈
                            (poly-obj P y .fam .subst (project-≈ P e) ∘ project-fam P x)
      project-fam-natural Poly.one _ = isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural (Poly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural Poly.var {inF i₁} {inF i₂} eq =
        begin
          (alg .famf .transf (project-idx Q i₂) ∘ project-fam Q i₂) ∘ WFam-subst Q eq
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (project-idx Q i₂) ∘ (project-fam Q i₂ ∘ WFam-subst Q eq)
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
      project-fam-natural (P Poly.+ Q) {inj₁ _} {inj₁ _} e = project-fam-natural P e
      project-fam-natural (P Poly.+ Q) {inj₂ _} {inj₂ _} e = project-fam-natural Q e
      project-fam-natural (P Poly.× Q) {x₁ , z₁} {x₂ , z₂} (e , f) =
        begin
          prod-m (project-fam P x₂) (project-fam Q z₂) ∘ prod-m _ _
        ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
          prod-m (project-fam P x₂ ∘ _) (project-fam Q z₂ ∘ _)
        ≈⟨ prod-m-cong (project-fam-natural P e) (project-fam-natural Q f) ⟩
          prod-m (_ ∘ project-fam P x₁) (_ ∘ project-fam Q z₁)
        ≈⟨ pair-functorial _ _ _ _ ⟩
          prod-m _ _ ∘ prod-m (project-fam P x₁) (project-fam Q z₁)
        ∎ where open ≈-Reasoning isEquiv

      fold : Mor WObj y
      fold .idxf .PS._⇒_.func (inF i)                   = alg .idxf .PS._⇒_.func (project-idx Q i)
      fold .idxf .PS._⇒_.func-resp-≈ {inF _} {inF _} eq = alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)
      fold .famf .transf (inF i)                        = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      fold .famf .natural {inF _} {inF _} eq            = project-fam-natural Poly.var eq

  hasMu : HasMu
  hasMu .HasMu.μ Q       = W-types.WObj Q
  hasMu .HasMu.inF Q     = W-types.inF-mor Q
  hasMu .HasMu.⦅_⦆ {Q}   = W-types.fold Q
