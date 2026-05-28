{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction. Builds initial algebras (μ-types)
-- for polynomial functors over Fam(𝒞) using setoid-indexed W-types.
------------------------------------------------------------------------------

open import Level using (_⊔_; suc; lift)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_; tt)
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts; strong-coproducts→coproducts;
         coKleisli-prod)
open import prop-setoid as PS
  using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_; changeCat)
import fam
import polynomial-functor
open polynomial-functor using (Poly; module Interp)

open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_)

module fam-mu-types where

module _ {o e} where
  open import Data.Sum using (_⊎_)
  open import Data.Product using () renaming (_×_ to _×T_)
  open import prop using (_∧_; ⊤; ⊥)

  ------------------------------------------------------------------------------
  -- Syntactic representation of polynomial functor but with constant slots holding a setoid rather than a
  -- category object. Used to define the W-type carrier of HasMu by structural recursion.
  data IdxPoly : Set (suc (o ⊔ e)) where
    param : Setoid o e → IdxPoly
    var  : IdxPoly
    _+_  : IdxPoly → IdxPoly → IdxPoly
    _×_  : IdxPoly → IdxPoly → IdxPoly

  -- Well-founded tree carrier (Martin-Löf W-types).
  mutual
    -- P-shaped trees.
    data W (P : IdxPoly) : Set o where
      inF : WIdx P P → W P

    WIdx : IdxPoly → IdxPoly → Set o
    WIdx P (param A)   = Carrier A
    WIdx P var         = W P
    WIdx P (Q₁ + Q₂)   = WIdx P Q₁ ⊎ WIdx P Q₂
    WIdx P (Q₁ × Q₂)   = WIdx P Q₁ ×T WIdx P Q₂

  mutual
    -- Tree equality by structural recursion on the polynomial.
    W-≈ : (P : IdxPoly) → W P → W P → Prop e
    W-≈ P (inF i₁) (inF i₂) = WIdx-≈ P P i₁ i₂

    WIdx-≈ : (P Q : IdxPoly) → WIdx P Q → WIdx P Q → Prop e
    WIdx-≈ P (param A)   x          y          = _≈s_ A x y
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
    WIdx-≈-refl P (param A) {x}         = IsEquivalence.refl (Setoid.isEquivalence A) {x}
    WIdx-≈-refl P var       {w}         = W-≈-refl P {w}
    WIdx-≈-refl P (Q₁ + Q₂) {inj₁ x}    = WIdx-≈-refl P Q₁ {x}
    WIdx-≈-refl P (Q₁ + Q₂) {inj₂ y}    = WIdx-≈-refl P Q₂ {y}
    WIdx-≈-refl P (Q₁ × Q₂) {x , y}     = WIdx-≈-refl P Q₁ {x} , WIdx-≈-refl P Q₂ {y}

  mutual
    W-≈-sym : ∀ P {w₁ w₂} → W-≈ P w₁ w₂ → W-≈ P w₂ w₁
    W-≈-sym P {inF i₁} {inF i₂} i₁≈i₂ = WIdx-≈-sym P P {i₁} {i₂} i₁≈i₂

    WIdx-≈-sym : ∀ P Q {x y} → WIdx-≈ P Q x y → WIdx-≈ P Q y x
    WIdx-≈-sym P (param A) {x} {y} x≈y = IsEquivalence.sym (Setoid.isEquivalence A) x≈y
    WIdx-≈-sym P var {w₁} {w₂} w₁≈w₂ = W-≈-sym P {w₁} {w₂} w₁≈w₂
    WIdx-≈-sym P (Q₁ + Q₂) {inj₁ x₁} {inj₁ x₂} x₁≈x₂ = WIdx-≈-sym P Q₁ x₁≈x₂
    WIdx-≈-sym P (Q₁ + Q₂) {inj₂ y₁} {inj₂ y₂} y₁≈y₂ = WIdx-≈-sym P Q₂ y₁≈y₂
    WIdx-≈-sym P (Q₁ × Q₂) {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = WIdx-≈-sym P Q₁ x₁≈x₂ , WIdx-≈-sym P Q₂ y₁≈y₂

  mutual
    W-≈-trans : ∀ P {w₁ w₂ w₃} → W-≈ P w₁ w₂ → W-≈ P w₂ w₃ → W-≈ P w₁ w₃
    W-≈-trans P {inF _} {inF _} {inF _} w₁≈w₂ w₂≈w₃ = WIdx-≈-trans P P w₁≈w₂ w₂≈w₃

    WIdx-≈-trans : ∀ P Q {x y z} →
                      WIdx-≈ P Q x y → WIdx-≈ P Q y z → WIdx-≈ P Q x z
    WIdx-≈-trans P (param A) {x} {y} {z} x≈y y≈z = IsEquivalence.trans (Setoid.isEquivalence A) x≈y y≈z
    WIdx-≈-trans P var {x} {y} {z} x≈y y≈z = W-≈-trans P {x} {y} {z} x≈y y≈z
    WIdx-≈-trans P (Q₁ + Q₂) {inj₁ _} {inj₁ _} {inj₁ _} x≈y y≈z = WIdx-≈-trans P Q₁ x≈y y≈z
    WIdx-≈-trans P (Q₁ + Q₂) {inj₂ _} {inj₂ _} {inj₂ _} x≈y y≈z = WIdx-≈-trans P Q₂ x≈y y≈z
    WIdx-≈-trans P (Q₁ × Q₂) {_ , _} {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) (y₁≈z₁ , y₂≈z₂) =
      WIdx-≈-trans P Q₁ x₁≈y₁ y₁≈z₁ , WIdx-≈-trans P Q₂ x₂≈y₂ y₂≈z₂

  WSetoid : IdxPoly → Setoid o e
  WSetoid P .Carrier = W P
  WSetoid P ._≈s_ = W-≈ P
  WSetoid P .Setoid.isEquivalence .IsEquivalence.refl {w}             = W-≈-refl P {w}
  WSetoid P .Setoid.isEquivalence .IsEquivalence.sym {w₁} {w₂}        = W-≈-sym P {w₁} {w₂}
  WSetoid P .Setoid.isEquivalence .IsEquivalence.trans {w₁} {w₂} {w₃} = W-≈-trans P {w₁} {w₂} {w₃}

------------------------------------------------------------------------------
-- HasMu instance for the Fam construction.
module WFam {o m e} (os es : _) {𝒞 : Category o m e} (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where
  open Category 𝒞
  open IsEquivalence
  open HasTerminal
  open HasProducts P
  open fam.CategoryOfFamilies os es 𝒞
  open Obj
  open Mor
  open Fam
  private module Fam𝒞 = Category cat
  open products P  -- Fam-level products
  private module Fam𝒞-P = HasProducts products
  open _⇒f_
  open Interp (terminal T) products strongCoproducts

  ----------------------------------------------------------------------
  -- Generic μ-types in Fam(𝒞), for polynomials Q : Poly cat. The idx side is WSetoid of Q (projecting param
  -- slots from Fam-objs to their idx setoids); the fibre side is built recursively over Q using 𝒞's products.
  module W-types (Q : Poly cat) where
    open Obj
    open Mor
    open Fam

    idx-of : Poly cat → IdxPoly
    idx-of (Poly.const A)  = param (A .idx)
    idx-of Poly.var        = var
    idx-of (P Poly.+ Q)  = idx-of P + idx-of Q
    idx-of (P Poly.× Q)  = idx-of P × idx-of Q

    WFam-fm : (P : Poly cat) → WIdx (idx-of Q) (idx-of P) → obj
    WFam-fm (Poly.const A)    a        = A .fam .fm a
    WFam-fm Poly.var          (inF i)  = WFam-fm Q i
    WFam-fm (P Poly.+ Q)      (inj₁ x) = WFam-fm P x
    WFam-fm (P Poly.+ Q)      (inj₂ y) = WFam-fm Q y
    WFam-fm (P Poly.× Q)      (x , y)  = prod (WFam-fm P x) (WFam-fm Q y)

    WFam-subst : (P : Poly cat) → ∀ {x y} → WIdx-≈ (idx-of Q) (idx-of P) x y → WFam-fm P x ⇒ WFam-fm P y
    WFam-subst (Poly.const A) {x} {y} x≈y = A .fam .subst x≈y
    WFam-subst Poly.var {inF i₁} {inF i₂} i₁≈i₂ = WFam-subst Q i₁≈i₂
    WFam-subst (P Poly.+ Q) {inj₁ _} {inj₁ _} x≈y = WFam-subst P x≈y
    WFam-subst (P Poly.+ Q) {inj₂ _} {inj₂ _} x≈y = WFam-subst Q x≈y
    WFam-subst (P Poly.+ Q) {inj₁ _} {inj₂ _} ()
    WFam-subst (P Poly.+ Q) {inj₂ _} {inj₁ _} ()
    WFam-subst (P Poly.× Q) {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) =
      prod-m (WFam-subst P x₁≈y₁) (WFam-subst Q x₂≈y₂)

    WFam-refl* : (P : Poly cat) → ∀ {x} → WFam-subst P (WIdx-≈-refl (idx-of Q) (idx-of P) {x}) ≈ id _
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
                  (y≈z : WIdx-≈ (idx-of Q) (idx-of P) y z) (x≈y : WIdx-≈ (idx-of Q) (idx-of P) x y) →
                  WFam-subst P (WIdx-≈-trans (idx-of Q) (idx-of P) x≈y y≈z) ≈ (WFam-subst P y≈z ∘ WFam-subst P x≈y)
    WFam-trans* (Poly.const A) y≈z x≈y = A .fam .trans* y≈z x≈y
    WFam-trans* Poly.var {inF _} {inF _} {inF _} y≈z x≈y =
      WFam-trans* Q y≈z x≈y
    WFam-trans* (P Poly.+ Q) {inj₁ _} {inj₁ _} {inj₁ _} y≈z x≈y = WFam-trans* P y≈z x≈y
    WFam-trans* (P Poly.+ Q) {inj₂ _} {inj₂ _} {inj₂ _} y≈z x≈y = WFam-trans* Q y≈z x≈y
    WFam-trans* (P Poly.× Q) {_ , _} {_ , _} {_ , _} (y₁≈z₁ , y₂≈z₂) (x₁≈y₁ , x₂≈y₂) =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-trans* P y₁≈z₁ x₁≈y₁) (WFam-trans* Q y₂≈z₂ x₂≈y₂) ⟩
        prod-m (WFam-subst P y₁≈z₁ ∘ WFam-subst P x₁≈y₁) (WFam-subst Q y₂≈z₂ ∘ WFam-subst Q x₂≈y₂)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P y₁≈z₁) (WFam-subst Q y₂≈z₂) ∘ prod-m (WFam-subst P x₁≈y₁) (WFam-subst Q x₂≈y₂)
      ∎ where open ≈-Reasoning isEquiv

    WFam : Fam (WSetoid (idx-of Q)) 𝒞
    WFam .fm (inF i)                             = WFam-fm Q i
    WFam .subst {inF _} {inF _} i₁≈i₂            = WFam-subst Q i₁≈i₂
    WFam .refl* {inF _}                          = WFam-refl* Q
    WFam .trans* {inF _} {inF _} {inF _} y≈z x≈y = WFam-trans* Q y≈z x≈y

    WObj : Obj
    WObj .idx = WSetoid (idx-of Q)
    WObj .fam = WFam

    embed-idx : (P : Poly cat) → fobj P WObj .idx .Carrier → WIdx (idx-of Q) (idx-of P)
    embed-idx (Poly.const A)   a          = a
    embed-idx Poly.var         w          = w
    embed-idx (P Poly.+ Q)     (inj₁ x)   = inj₁ (embed-idx P x)
    embed-idx (P Poly.+ Q)     (inj₂ y)   = inj₂ (embed-idx Q y)
    embed-idx (P Poly.× Q)     (x , y)    = (embed-idx P x , embed-idx Q y)

    unembed-idx : (P : Poly cat) → WIdx (idx-of Q) (idx-of P) → fobj P WObj .idx .Carrier
    unembed-idx (Poly.const A)   a          = a
    unembed-idx Poly.var         w          = w
    unembed-idx (P Poly.+ Q)     (inj₁ x)   = inj₁ (unembed-idx P x)
    unembed-idx (P Poly.+ Q)     (inj₂ y)   = inj₂ (unembed-idx Q y)
    unembed-idx (P Poly.× Q)     (x , y)    = (unembed-idx P x , unembed-idx Q y)

    embed-≈ : (P : Poly cat) → ∀ {x y} →
              fobj P WObj .idx ._≈s_ x y → WIdx-≈ (idx-of Q) (idx-of P) (embed-idx P x) (embed-idx P y)
    embed-≈ (Poly.const A)   x≈y  = x≈y
    embed-≈ Poly.var         x≈y  = x≈y
    embed-≈ (P Poly.+ Q) {inj₁ _} {inj₁ _} x≈y            = embed-≈ P x≈y
    embed-≈ (P Poly.+ Q) {inj₂ _} {inj₂ _} x≈y            = embed-≈ Q x≈y
    embed-≈ (P Poly.× Q) {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂)  = (embed-≈ P x₁≈y₁ , embed-≈ Q x₂≈y₂)

    unembed-≈ : (P : Poly cat) → ∀ {x y} →
                WIdx-≈ (idx-of Q) (idx-of P) x y → fobj P WObj .idx ._≈s_ (unembed-idx P x) (unembed-idx P y)
    unembed-≈ (Poly.const A)   x≈y  = x≈y
    unembed-≈ Poly.var         x≈y  = x≈y
    unembed-≈ (P Poly.+ Q) {inj₁ _} {inj₁ _} x≈y           = unembed-≈ P x≈y
    unembed-≈ (P Poly.+ Q) {inj₂ _} {inj₂ _} x≈y           = unembed-≈ Q x≈y
    unembed-≈ (P Poly.× Q) {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) = (unembed-≈ P x₁≈y₁ , unembed-≈ Q x₂≈y₂)

    embed-unembed-id : (P : Poly cat) (i : WIdx (idx-of Q) (idx-of P)) →
                       WIdx-≈ (idx-of Q) (idx-of P) (embed-idx P (unembed-idx P i)) i
    embed-unembed-id (Poly.const A) a         = A .idx .isEquivalence .refl
    embed-unembed-id Poly.var       w         = W-≈-refl (idx-of Q) {w}
    embed-unembed-id (P Poly.+ Q)   (inj₁ x)  = embed-unembed-id P x
    embed-unembed-id (P Poly.+ Q)   (inj₂ y)  = embed-unembed-id Q y
    embed-unembed-id (P Poly.× Q)   (x , y)   = (embed-unembed-id P x , embed-unembed-id Q y)

    unembed-embed-id : (P : Poly cat) (j : fobj P WObj .idx .Carrier) →
                       fobj P WObj .idx ._≈s_ (unembed-idx P (embed-idx P j)) j
    unembed-embed-id (Poly.const A) a         = A .idx .isEquivalence .refl
    unembed-embed-id Poly.var       (inF _)   = fobj Poly.var WObj .idx .isEquivalence .refl
    unembed-embed-id (P Poly.+ Q)   (inj₁ x)  = unembed-embed-id P x
    unembed-embed-id (P Poly.+ Q)   (inj₂ y)  = unembed-embed-id Q y
    unembed-embed-id (P Poly.× Q)   (x , y)   = (unembed-embed-id P x , unembed-embed-id Q y)

    embed-fam : (P : Poly cat) (i : fobj P WObj .idx .Carrier) →
                fobj P WObj .fam .fm i ⇒ WFam-fm P (embed-idx P i)
    embed-fam (Poly.const A)   a          = id _
    embed-fam Poly.var         (inF _)    = id _
    embed-fam (P Poly.+ Q)     (inj₁ x)   = embed-fam P x
    embed-fam (P Poly.+ Q)     (inj₂ y)   = embed-fam Q y
    embed-fam (P Poly.× Q)     (x , y)    = prod-m (embed-fam P x) (embed-fam Q y)

    embed-fam-natural : (P : Poly cat) → ∀ {x₁ x₂} (x₁≈x₂ : fobj P WObj .idx ._≈s_ x₁ x₂) →
                        (embed-fam P x₂ ∘ fobj P WObj .fam .subst x₁≈x₂) ≈
                        (WFam-subst P (embed-≈ P x₁≈x₂) ∘ embed-fam P x₁)
    embed-fam-natural (Poly.const A) _ = ≈-trans id-left (≈-sym id-right)
    embed-fam-natural Poly.var {inF _} {inF _} _ = ≈-trans id-left (≈-sym id-right)
    embed-fam-natural (P Poly.+ Q) {inj₁ _} {inj₁ _} x₁≈x₂ = embed-fam-natural P x₁≈x₂
    embed-fam-natural (P Poly.+ Q) {inj₂ _} {inj₂ _} x₁≈x₂ = embed-fam-natural Q x₁≈x₂
    embed-fam-natural (P Poly.× Q) {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) =
      begin
        prod-m (embed-fam P x₂) (embed-fam Q y₂) ∘ prod-m _ _
      ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
        prod-m (embed-fam P x₂ ∘ _) (embed-fam Q y₂ ∘ _)
      ≈⟨ prod-m-cong (embed-fam-natural P x₁≈x₂) (embed-fam-natural Q y₁≈y₂) ⟩
        prod-m (WFam-subst P (embed-≈ P x₁≈x₂) ∘ embed-fam P x₁) (WFam-subst Q (embed-≈ Q y₁≈y₂) ∘ embed-fam Q y₁)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P (embed-≈ P x₁≈x₂)) (WFam-subst Q (embed-≈ Q y₁≈y₂)) ∘ prod-m (embed-fam P x₁) (embed-fam Q y₁)
      ∎ where open ≈-Reasoning isEquiv

    unembed-fam : (P : Poly cat) (j : WIdx (idx-of Q) (idx-of P)) → WFam-fm P j ⇒ fobj P WObj .fam .fm (unembed-idx P j)
    unembed-fam (Poly.const A) _        = id _
    unembed-fam Poly.var       (inF _)  = id _
    unembed-fam (P Poly.+ Q)   (inj₁ x) = unembed-fam P x
    unembed-fam (P Poly.+ Q)   (inj₂ y) = unembed-fam Q y
    unembed-fam (P Poly.× Q)   (x , y)  = prod-m (unembed-fam P x) (unembed-fam Q y)

    embed-unembed-fam-id : (P : Poly cat) (j : WIdx (idx-of Q) (idx-of P)) →
                           (embed-fam P (unembed-idx P j) ∘ unembed-fam P j) ≈
                           WFam-subst P (WIdx-≈-sym (idx-of Q) (idx-of P) (embed-unembed-id P j))
    embed-unembed-fam-id (Poly.const A) _        = ≈-trans id-left (≈-sym (A .fam .refl*))
    embed-unembed-fam-id Poly.var       (inF j)  = ≈-trans id-left (≈-sym (WFam-refl* Q {j}))
    embed-unembed-fam-id (P Poly.+ Q')  (inj₁ x) = embed-unembed-fam-id P x
    embed-unembed-fam-id (P Poly.+ Q')  (inj₂ y) = embed-unembed-fam-id Q' y
    embed-unembed-fam-id (P Poly.× Q')  (x , y)  =
      ≈-trans (≈-sym (pair-functorial _ _ _ _))
                     (prod-m-cong (embed-unembed-fam-id P x) (embed-unembed-fam-id Q' y))

    inF-mor : Mor (fobj Q WObj) WObj
    inF-mor .idxf .PS._⇒_.func i            = inF (embed-idx Q i)
    inF-mor .idxf .PS._⇒_.func-resp-≈ x≈y   = embed-≈ Q x≈y
    inF-mor .famf .transf i                 = embed-fam Q i
    inF-mor .famf .natural x₁≈x₂            = embed-fam-natural Q x₁≈x₂

    -- Open (parametric) fold: takes algebra in extended context Γ ⊗ fobj Q y ⇒ y and produces Γ ⊗ μ Q ⇒ y.
    -- Threads γ through the structural recursion.
    module Fold {Γ y : Obj} (alg : Mor (Γ ⊗ fobj Q y) y) where
      open Obj
      open Mor

      project-idx : (P : Poly cat) → Γ .idx .Carrier → WIdx (idx-of Q) (idx-of P) → fobj P y .idx .Carrier
      project-idx (Poly.const A) _ a         = a
      project-idx Poly.var       γ (inF i)   =
        alg .idxf .PS._⇒_.func (γ , project-idx Q γ i)
      project-idx (P Poly.+ R)   γ (inj₁ x)  = inj₁ (project-idx P γ x)
      project-idx (P Poly.+ R)   γ (inj₂ z)  = inj₂ (project-idx R γ z)
      project-idx (P Poly.× R)   γ (x , z)   = (project-idx P γ x , project-idx R γ z)

      project-≈ : (P : Poly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
                  (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂) (i₁≈i₂ : WIdx-≈ (idx-of Q) (idx-of P) x z) →
                  fobj P y .idx ._≈s_ (project-idx P γ₁ x) (project-idx P γ₂ z)
      project-≈ (Poly.const A) _ x≈z = x≈z
      project-≈ Poly.var {γ₁} {γ₂} {inF _} {inF _} γ₁≈γ₂ x≈z =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈ Q γ₁≈γ₂ x≈z)
      project-≈ (P Poly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ x≈z = project-≈ P γ₁≈γ₂ x≈z
      project-≈ (P Poly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ x≈z = project-≈ R γ₁≈γ₂ x≈z
      project-≈ (P Poly.× R) {x = _ , _} {_ , _} γ₁≈γ₂ (x₁≈z₁ , x₂≈z₂) =
        project-≈ P γ₁≈γ₂ x₁≈z₁ , project-≈ R γ₁≈γ₂ x₂≈z₂

      project-fam : (P : Poly cat) (γ : Γ .idx .Carrier) (i : WIdx (idx-of Q) (idx-of P)) →
                    prod (Γ .fam .fm γ) (WFam-fm P i) ⇒ fobj P y .fam .fm (project-idx P γ i)
      project-fam (Poly.const A)   _ _         = p₂
      project-fam Poly.var         γ (inF i)   =
        alg .famf .transf (γ , project-idx Q γ i) ∘ pair p₁ (project-fam Q γ i)
      project-fam (P Poly.+ R)     γ (inj₁ x)  = project-fam P γ x
      project-fam (P Poly.+ R)     γ (inj₂ z)  = project-fam R γ z
      project-fam (P Poly.× R)     γ (x , z)   =
        pair (project-fam P γ x ∘ pair p₁ (p₁ ∘ p₂)) (project-fam R γ z ∘ pair p₁ (p₂ ∘ p₂))

      project-fam-natural : (P : Poly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
                            (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂) (i₁≈i₂ : WIdx-≈ (idx-of Q) (idx-of P) x z) →
                            project-fam P γ₂ z ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂) ≈
                            fobj P y .fam .subst (project-≈ P γ₁≈γ₂ i₁≈i₂) ∘ project-fam P γ₁ x
      project-fam-natural (Poly.const A) {x = a} {z = b} _ i₁≈i₂ =
        begin
          p₂ ∘ prod-m _ (A .fam .subst i₁≈i₂)
        ≈⟨ pair-p₂ _ _ ⟩
          A .fam .subst i₁≈i₂ ∘ p₂
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural Poly.var {γ₁} {γ₂} {inF i₁} {inF i₂} γ₁≈γ₂ i₁≈i₂ =
        begin
          (alg .famf .transf (γ₂ , _) ∘ pair p₁ (project-fam Q γ₂ i₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂)
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (γ₂ , _) ∘
            (pair p₁ (project-fam Q γ₂ i₂) ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂))
        ≈⟨ ∘-cong (≈-refl) (pair-natural _ _ _) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (p₁ ∘ prod-m _ _) (project-fam Q γ₂ i₂ ∘ prod-m _ _)
        ≈⟨ ∘-cong (≈-refl) (pair-cong (pair-p₁ _ _) (project-fam-natural Q γ₁≈γ₂ i₁≈i₂)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁)
                 (fobj Q y .fam .subst (project-≈ Q γ₁≈γ₂ i₁≈i₂) ∘ project-fam Q γ₁ i₁)
        ≈⟨ ≈-sym (∘-cong (≈-refl) (pair-compose _ _ _ _)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            (prod-m (Γ .fam .subst γ₁≈γ₂) (fobj Q y .fam .subst (project-≈ Q γ₁≈γ₂ i₁≈i₂))
              ∘ pair p₁ (project-fam Q γ₁ i₁))
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (γ₂ , _) ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (fobj Q y .fam .subst (project-≈ Q γ₁≈γ₂ i₁≈i₂)))
            ∘ pair p₁ (project-fam Q γ₁ i₁)
        ≈⟨ ∘-cong (alg .famf .natural (γ₁≈γ₂ , project-≈ Q γ₁≈γ₂ i₁≈i₂)) (≈-refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈ Q γ₁≈γ₂ i₁≈i₂))
            ∘ alg .famf .transf (γ₁ , _)) ∘ pair p₁ (project-fam Q γ₁ i₁)
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈ Q γ₁≈γ₂ i₁≈i₂))
            ∘ (alg .famf .transf (γ₁ , _) ∘ pair p₁ (project-fam Q γ₁ i₁))
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural (P Poly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural P γ₁≈γ₂ i₁≈i₂
      project-fam-natural (P Poly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural R γ₁≈γ₂ i₁≈i₂
      project-fam-natural (P Poly.× R) {γ₁} {γ₂} {x₁ , z₁} {x₂ , z₂} γ₁≈γ₂ (x₁≈x₂ , z₁≈z₂) =
        begin
          pair (project-fam P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂)) (project-fam R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (prod-m (WFam-subst P x₁≈x₂) (WFam-subst R z₁≈z₂))
        ≈⟨ pair-natural _ _ _ ⟩
          pair ((project-fam P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂)) ∘ prod-m _ _)
               ((project-fam R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂)) ∘ prod-m _ _)
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (project-fam P γ₂ x₂ ∘ (pair p₁ (p₁ ∘ p₂) ∘ prod-m _ _))
               (project-fam R γ₂ z₂ ∘ (pair p₁ (p₂ ∘ p₂) ∘ prod-m _ _))
        ≈⟨ pair-cong
             (∘-cong (≈-refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (≈-refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _)) (≈-trans (∘-cong (pair-p₁ _ _) (≈-refl)) (assoc _ _ _))))))))
             (∘-cong (≈-refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (≈-refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₂ _ _) (≈-refl)) (assoc _ _ _)))))))) ⟩
          pair (project-fam P γ₂ x₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst P x₁≈x₂ ∘ (p₁ ∘ p₂)))
               (project-fam R γ₂ z₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst R z₁≈z₂ ∘ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (∘-cong (≈-refl) (≈-sym (pair-compose _ _ _ _)))
                     (∘-cong (≈-refl) (≈-sym (pair-compose _ _ _ _))) ⟩
          pair (project-fam P γ₂ x₂ ∘ (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P x₁≈x₂) ∘ pair p₁ (p₁ ∘ p₂)))
               (project-fam R γ₂ z₂ ∘ (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst R z₁≈z₂) ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
          pair ((project-fam P γ₂ x₂ ∘ prod-m _ _) ∘ pair p₁ (p₁ ∘ p₂))
               ((project-fam R γ₂ z₂ ∘ prod-m _ _) ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (∘-cong (project-fam-natural P γ₁≈γ₂ x₁≈x₂) (≈-refl))
                     (∘-cong (project-fam-natural R γ₁≈γ₂ z₁≈z₂) (≈-refl)) ⟩
          pair ((fobj P y .fam .subst (project-≈ P γ₁≈γ₂ x₁≈x₂) ∘ project-fam P γ₁ x₁) ∘ pair p₁ (p₁ ∘ p₂))
               ((fobj R y .fam .subst (project-≈ R γ₁≈γ₂ z₁≈z₂) ∘ project-fam R γ₁ z₁) ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (fobj P y .fam .subst (project-≈ P γ₁≈γ₂ x₁≈x₂) ∘ (project-fam P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂)))
               (fobj R y .fam .subst (project-≈ R γ₁≈γ₂ z₁≈z₂) ∘ (project-fam R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ ≈-sym (pair-compose _ _ _ _) ⟩
          prod-m (fobj P y .fam .subst (project-≈ P γ₁≈γ₂ x₁≈x₂)) (fobj R y .fam .subst (project-≈ R γ₁≈γ₂ z₁≈z₂))
            ∘ pair (project-fam P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂)) (project-fam R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂))
        ∎ where open ≈-Reasoning isEquiv

      fold : Mor (Γ ⊗ WObj) y
      fold .idxf .PS._⇒_.func (γ , inF i) =
        alg .idxf .PS._⇒_.func (γ , project-idx Q γ i)
      fold .idxf .PS._⇒_.func-resp-≈ {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈ Q γ₁≈γ₂ i₁≈i₂)
      fold .famf .transf (γ , inF i) =
        alg .famf .transf (γ , project-idx Q γ i) ∘
          pair p₁ (project-fam Q γ i)
      fold .famf .natural {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        project-fam-natural Poly.var γ₁≈γ₂ i₁≈i₂

      -- project-idx through embed-idx agrees with fmor's idx action of fold.
      β-idx : (P : Poly cat) {γ₁ γ₂ : Γ .idx .Carrier} (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂)
              {i₁ i₂ : fobj P WObj .idx .Carrier} (i₁≈i₂ : fobj P WObj .idx ._≈s_ i₁ i₂) →
              fobj P y .idx ._≈s_ (project-idx P γ₁ (embed-idx P i₁)) (fmor P fold .idxf .PS._⇒_.func (γ₂ , i₂))
      β-idx (Poly.const A) _ i₁≈i₂                        = i₁≈i₂
      β-idx Poly.var       γ₁≈γ₂ {inF _} {inF _} i₁≈i₂    =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈ Q γ₁≈γ₂ i₁≈i₂)
      β-idx (P Poly.+ R)   γ₁≈γ₂ {inj₁ _} {inj₁ _} i₁≈i₂  = β-idx P γ₁≈γ₂ i₁≈i₂
      β-idx (P Poly.+ R)   γ₁≈γ₂ {inj₂ _} {inj₂ _} i₁≈i₂  = β-idx R γ₁≈γ₂ i₁≈i₂
      β-idx (P Poly.× R)   γ₁≈γ₂ (x₁≈x₂ , z₁≈z₂)          = β-idx P γ₁≈γ₂ x₁≈x₂ , β-idx R γ₁≈γ₂ z₁≈z₂

      -- project-fam through embed agrees (modulo subst from β-idx) with fmor's fam action of fold.
      β-fam : (P : Poly cat) (γ : Γ .idx .Carrier) (i : fobj P WObj .idx .Carrier) →
              (fobj P y .fam .subst (β-idx P (Γ .idx .Setoid.refl) (fobj P WObj .idx .Setoid.refl)) ∘
                project-fam P γ (embed-idx P i) ∘ pair p₁ (embed-fam P i ∘ p₂))
            ≈ fmor P fold .famf .transf (γ , i)
      β-fam (Poly.const A) γ i = begin
          (A .fam .subst _ ∘ p₂) ∘ pair p₁ (id _ ∘ p₂)
        ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
          (A .fam .subst _ ∘ p₂) ∘ pair p₁ p₂
        ≈⟨ assoc _ _ _ ⟩
          A .fam .subst _ ∘ (p₂ ∘ pair p₁ p₂)
        ≈⟨ ∘-cong ≈-refl (pair-p₂ _ _) ⟩
          A .fam .subst _ ∘ p₂
        ≈⟨ ∘-cong (A .fam .refl*) ≈-refl ⟩
          id _ ∘ p₂
        ≈⟨ id-left ⟩
          p₂
        ∎ where open ≈-Reasoning isEquiv
      β-fam Poly.var γ (inF i) = begin
          (y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx Q γ i) ∘ pair p₁ (project-fam Q γ i))) ∘ pair p₁ (id _ ∘ p₂)
        ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
          (y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx Q γ i) ∘ pair p₁ (project-fam Q γ i))) ∘ pair p₁ p₂
        ≈⟨ ∘-cong ≈-refl (≈-trans (pair-cong (≈-sym id-right) (≈-sym id-right)) (pair-ext (id _))) ⟩
          (y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx Q γ i) ∘ pair p₁ (project-fam Q γ i))) ∘ id _
        ≈⟨ id-right ⟩
          y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx Q γ i) ∘ pair p₁ (project-fam Q γ i))
        ≈⟨ ∘-cong (y .fam .refl*) ≈-refl ⟩
          id _ ∘ (alg .famf .transf (γ , project-idx Q γ i) ∘ pair p₁ (project-fam Q γ i))
        ≈⟨ id-left ⟩
          alg .famf .transf (γ , project-idx Q γ i) ∘ pair p₁ (project-fam Q γ i)
        ∎ where open ≈-Reasoning isEquiv
      β-fam (P Poly.+ R) γ (inj₁ x) = ≈-trans (β-fam P γ x) (≈-sym (≈-trans id-left id-left))
      β-fam (P Poly.+ R) γ (inj₂ z) = ≈-trans (β-fam R γ z) (≈-sym (≈-trans id-left id-left))
      β-fam (P Poly.× R) γ (x , z)  =
        ≈-trans (∘-cong (pair-natural _ _ _) ≈-refl) (≈-trans (pair-natural _ _ _) (pair-cong eq-P eq-R))
        where
          -- Lift WObj-fibre pair into WFam-fibre form.
          pair-embed : prod (Γ .fam .fm γ) (prod (fobj P WObj .fam .fm x) (fobj R WObj .fam .fm z)) ⇒
                       prod (Γ .fam .fm γ) (prod (WFam-fm P (embed-idx P x)) (WFam-fm R (embed-idx R z)))
          pair-embed = pair p₁ (pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂) ∘ p₂)

          bridge-P : (pair p₁ (p₁ ∘ p₂) ∘ pair-embed) ≈ pair p₁ (embed-fam P x ∘ (p₁ ∘ p₂))
          bridge-P = begin
              pair p₁ (p₁ ∘ p₂) ∘ pair-embed
            ≈⟨ pair-natural _ _ _ ⟩
              pair (p₁ ∘ pair-embed) ((p₁ ∘ p₂) ∘ pair-embed)
            ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
              pair p₁ (p₁ ∘ (p₂ ∘ pair-embed))
            ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
              pair p₁ (p₁ ∘ (pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂) ∘ p₂))
            ≈⟨ pair-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
              pair p₁ ((p₁ ∘ pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂)) ∘ p₂)
            ≈⟨ pair-cong ≈-refl (∘-cong (pair-p₁ _ _) ≈-refl) ⟩
              pair p₁ ((embed-fam P x ∘ p₁) ∘ p₂)
            ≈⟨ pair-cong ≈-refl (assoc _ _ _) ⟩
              pair p₁ (embed-fam P x ∘ (p₁ ∘ p₂))
            ∎ where open ≈-Reasoning isEquiv

          bridge-R : (pair p₁ (p₂ ∘ p₂) ∘ pair-embed) ≈ pair p₁ (embed-fam R z ∘ (p₂ ∘ p₂))
          bridge-R = begin
              pair p₁ (p₂ ∘ p₂) ∘ pair-embed
            ≈⟨ pair-natural _ _ _ ⟩
              pair (p₁ ∘ pair-embed) ((p₂ ∘ p₂) ∘ pair-embed)
            ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
              pair p₁ (p₂ ∘ (p₂ ∘ pair-embed))
            ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
              pair p₁ (p₂ ∘ (pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂) ∘ p₂))
            ≈⟨ pair-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
              pair p₁ ((p₂ ∘ pair (embed-fam P x ∘ p₁) (embed-fam R z ∘ p₂)) ∘ p₂)
            ≈⟨ pair-cong ≈-refl (∘-cong (pair-p₂ _ _) ≈-refl) ⟩
              pair p₁ ((embed-fam R z ∘ p₂) ∘ p₂)
            ≈⟨ pair-cong ≈-refl (assoc _ _ _) ⟩
              pair p₁ (embed-fam R z ∘ (p₂ ∘ p₂))
            ∎ where open ≈-Reasoning isEquiv

          eq-P : ((fobj P y .fam .subst _ ∘ p₁) ∘
                    pair (project-fam P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                         (project-fam R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
                 ≈ id _ ∘ (fmor P fold .famf .transf (γ , x) ∘ pair p₁ (id _ ∘ (p₁ ∘ p₂)))
          eq-P = begin
              ((fobj P y .fam .subst _ ∘ p₁) ∘
                pair (project-fam P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                     (project-fam R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
            ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
              (fobj P y .fam .subst _ ∘ (p₁ ∘
                pair (project-fam P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                     (project-fam R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂)))) ∘ pair-embed
            ≈⟨ ∘-cong (∘-cong ≈-refl (pair-p₁ _ _)) ≈-refl ⟩
              (fobj P y .fam .subst _ ∘ (project-fam P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))) ∘ pair-embed
            ≈⟨ ∘-cong (≈-sym (assoc _ _ _)) ≈-refl ⟩
              ((fobj P y .fam .subst _ ∘ project-fam P γ (embed-idx P x)) ∘ pair p₁ (p₁ ∘ p₂)) ∘ pair-embed
            ≈⟨ assoc _ _ _ ⟩
              (fobj P y .fam .subst _ ∘ project-fam P γ (embed-idx P x)) ∘ (pair p₁ (p₁ ∘ p₂) ∘ pair-embed)
            ≈⟨ ∘-cong ≈-refl bridge-P ⟩
              (fobj P y .fam .subst _ ∘ project-fam P γ (embed-idx P x)) ∘
                pair p₁ (embed-fam P x ∘ (p₁ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _))) ⟩
              (fobj P y .fam .subst _ ∘ project-fam P γ (embed-idx P x)) ∘
                pair p₁ (embed-fam P x ∘ (p₂ ∘ pair p₁ (p₁ ∘ p₂)))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl (assoc _ _ _)) ⟩
              (fobj P y .fam .subst _ ∘ project-fam P γ (embed-idx P x)) ∘
                pair p₁ ((embed-fam P x ∘ p₂) ∘ pair p₁ (p₁ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong (pair-p₁ _ _) ≈-refl) ⟩
              (fobj P y .fam .subst _ ∘ project-fam P γ (embed-idx P x)) ∘
                pair (p₁ ∘ pair p₁ (p₁ ∘ p₂)) ((embed-fam P x ∘ p₂) ∘ pair p₁ (p₁ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-natural _ _ _) ⟩
              (fobj P y .fam .subst _ ∘ project-fam P γ (embed-idx P x)) ∘
                (pair p₁ (embed-fam P x ∘ p₂) ∘ pair p₁ (p₁ ∘ p₂))
            ≈˘⟨ assoc _ _ _ ⟩
              ((fobj P y .fam .subst _ ∘ project-fam P γ (embed-idx P x)) ∘
                pair p₁ (embed-fam P x ∘ p₂)) ∘ pair p₁ (p₁ ∘ p₂)
            ≈⟨ ∘-cong (β-fam P γ x) ≈-refl ⟩
              fmor P fold .famf .transf (γ , x) ∘ pair p₁ (p₁ ∘ p₂)
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
              fmor P fold .famf .transf (γ , x) ∘ pair p₁ (id _ ∘ (p₁ ∘ p₂))
            ≈˘⟨ id-left ⟩
              id _ ∘ (fmor P fold .famf .transf (γ , x) ∘ pair p₁ (id _ ∘ (p₁ ∘ p₂)))
            ∎ where open ≈-Reasoning isEquiv

          eq-R : ((fobj R y .fam .subst _ ∘ p₂) ∘
                    pair (project-fam P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                         (project-fam R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
               ≈ id _ ∘ (fmor R fold .famf .transf (γ , z) ∘ pair p₁ (id _ ∘ (p₂ ∘ p₂)))
          eq-R =
            begin
              ((fobj R y .fam .subst _ ∘ p₂) ∘
                pair (project-fam P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                     (project-fam R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
            ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
              (fobj R y .fam .subst _ ∘ (p₂ ∘
                pair (project-fam P γ (embed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                     (project-fam R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂)))) ∘ pair-embed
            ≈⟨ ∘-cong (∘-cong ≈-refl (pair-p₂ _ _)) ≈-refl ⟩
              (fobj R y .fam .subst _ ∘ (project-fam R γ (embed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘ pair-embed
            ≈⟨ ∘-cong (≈-sym (assoc _ _ _)) ≈-refl ⟩
              ((fobj R y .fam .subst _ ∘ project-fam R γ (embed-idx R z)) ∘ pair p₁ (p₂ ∘ p₂)) ∘ pair-embed
            ≈⟨ assoc _ _ _ ⟩
              (fobj R y .fam .subst _ ∘ project-fam R γ (embed-idx R z)) ∘ (pair p₁ (p₂ ∘ p₂) ∘ pair-embed)
            ≈⟨ ∘-cong ≈-refl bridge-R ⟩
              (fobj R y .fam .subst _ ∘ project-fam R γ (embed-idx R z)) ∘
                pair p₁ (embed-fam R z ∘ (p₂ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _))) ⟩
              (fobj R y .fam .subst _ ∘ project-fam R γ (embed-idx R z)) ∘
                pair p₁ (embed-fam R z ∘ (p₂ ∘ pair p₁ (p₂ ∘ p₂)))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl (assoc _ _ _)) ⟩
              (fobj R y .fam .subst _ ∘ project-fam R γ (embed-idx R z)) ∘
                pair p₁ ((embed-fam R z ∘ p₂) ∘ pair p₁ (p₂ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-cong (pair-p₁ _ _) ≈-refl) ⟩
              (fobj R y .fam .subst _ ∘ project-fam R γ (embed-idx R z)) ∘
                pair (p₁ ∘ pair p₁ (p₂ ∘ p₂)) ((embed-fam R z ∘ p₂) ∘ pair p₁ (p₂ ∘ p₂))
            ≈˘⟨ ∘-cong ≈-refl (pair-natural _ _ _) ⟩
              (fobj R y .fam .subst _ ∘ project-fam R γ (embed-idx R z)) ∘
                (pair p₁ (embed-fam R z ∘ p₂) ∘ pair p₁ (p₂ ∘ p₂))
            ≈˘⟨ assoc _ _ _ ⟩
              ((fobj R y .fam .subst _ ∘ project-fam R γ (embed-idx R z)) ∘
                pair p₁ (embed-fam R z ∘ p₂)) ∘ pair p₁ (p₂ ∘ p₂)
            ≈⟨ ∘-cong (β-fam R γ z) ≈-refl ⟩
              fmor R fold .famf .transf (γ , z) ∘ pair p₁ (p₂ ∘ p₂)
            ≈˘⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
              fmor R fold .famf .transf (γ , z) ∘ pair p₁ (id _ ∘ (p₂ ∘ p₂))
            ≈˘⟨ id-left ⟩
              id _ ∘ (fmor R fold .famf .transf (γ , z) ∘ pair p₁ (id _ ∘ (p₂ ∘ p₂)))
            ∎ where open ≈-Reasoning isEquiv

      -- Cata helpers (η case): given h with h-step, build proof h ≃ fold.
      module _ (h : Mor (Γ ⊗ WObj) y)
               (h-step : (h Fam𝒞.∘ Fam𝒞-P.pair Fam𝒞-P.p₁ (inF-mor Fam𝒞.∘ Fam𝒞-P.p₂)) ≃
                         (alg Fam𝒞.∘ Fam𝒞-P.pair Fam𝒞-P.p₁ (fmor Q h))) where
        η-idx : (P : Poly cat) {δ₁ δ₂ : Γ .idx .Carrier} (δ₁≈δ₂ : Γ .idx ._≈s_ δ₁ δ₂)
                {j₁ j₂ : WIdx (idx-of Q) (idx-of P)} (j₁≈j₂ : WIdx-≈ (idx-of Q) (idx-of P) j₁ j₂) →
                fobj P y .idx ._≈s_ (fmor P h .idxf .PS._⇒_.func (δ₁ , unembed-idx P j₁)) (project-idx P δ₂ j₂)
        η-idx (Poly.const A) _ j₁≈j₂ = j₁≈j₂
        η-idx Poly.var δ₁≈δ₂ {inF j₁} {inF j₂} j₁≈j₂ =
          begin
            h .idxf .PS._⇒_.func (_ , inF j₁)
          ≈⟨ h .idxf .PS._⇒_.func-resp-≈
               (δ₁≈δ₂ ,
                WObj .idx .isEquivalence .trans j₁≈j₂ (WObj .idx .isEquivalence .sym (embed-unembed-id Q j₂))) ⟩
            h .idxf .PS._⇒_.func (_ , inF (embed-idx Q (unembed-idx Q j₂)))
          ≈⟨ h-step ._≃_.idxf-eq .PS._≃m_.func-eq
               (Γ .idx .isEquivalence .refl , fobj Q WObj .idx .isEquivalence .refl) ⟩
            alg .idxf .PS._⇒_.func (_ , fmor Q h .idxf .PS._⇒_.func (_ , unembed-idx Q j₂))
          ≈⟨ alg .idxf .PS._⇒_.func-resp-≈
               (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q)))) ⟩
            alg .idxf .PS._⇒_.func (_ , project-idx Q _ j₂)
          ∎ where open ≈-Reasoning (y .idx .isEquivalence)
        η-idx (P Poly.+ R) δ₁≈δ₂ {inj₁ x₁} {inj₁ x₂} j₁≈j₂ = η-idx P δ₁≈δ₂ j₁≈j₂
        η-idx (P Poly.+ R) δ₁≈δ₂ {inj₂ y₁} {inj₂ y₂} j₁≈j₂ = η-idx R δ₁≈δ₂ j₁≈j₂
        η-idx (P Poly.× R) δ₁≈δ₂ {x₁ , z₁} {x₂ , z₂} (x₁≈x₂ , z₁≈z₂) =
          η-idx P δ₁≈δ₂ x₁≈x₂ , η-idx R δ₁≈δ₂ z₁≈z₂

        -- Fam-level analogue at WIdx level: relates fmor h's transf (bridged via unembed-fam) to
        -- project-fam (modulo subst from η-idx).
        η-fam : (P : Poly cat) (γ : Γ .idx .Carrier) (j : WIdx (idx-of Q) (idx-of P)) →
                (fobj P y .fam .subst (η-idx P (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) (idx-of P) {j})) ∘
                 fmor P h .famf .transf (γ , unembed-idx P j) ∘ pair p₁ (unembed-fam P j ∘ p₂))
              ≈ project-fam P γ j
        η-fam (Poly.const A) γ j = begin
            (A .fam .subst _ ∘ p₂) ∘ pair p₁ (id _ ∘ p₂)
          ≈⟨ ∘-cong (∘-cong (A .fam .refl*) ≈-refl) ≈-refl ⟩
            (id _ ∘ p₂) ∘ pair p₁ (id _ ∘ p₂)
          ≈⟨ ∘-cong id-left ≈-refl ⟩
            p₂ ∘ pair p₁ (id _ ∘ p₂)
          ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl id-left) ⟩
            p₂ ∘ pair p₁ p₂
          ≈⟨ pair-p₂ _ _ ⟩
            p₂
          ∎ where open ≈-Reasoning isEquiv
        η-fam Poly.var γ (inF j) = begin
            (y .fam .subst _ ∘ h .famf .transf (γ , inF j) ∘ pair p₁ (id _ ∘ p₂))
          ≈⟨ ≈-trans (∘-cong ≈-refl (≈-trans (pair-cong ≈-refl id-left) pair-ext0)) id-right ⟩
            y .fam .subst _ ∘ h .famf .transf (γ , inF j)
          ≈⟨ ∘-cong (y .fam .trans*
                       (y .idx .isEquivalence .trans
                         (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                           (Γ .idx .isEquivalence .refl , fobj Q WObj .idx .isEquivalence .refl))
                         (alg .idxf .PS._⇒_.func-resp-≈
                           (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q))))))
                       (h .idxf .PS._⇒_.func-resp-≈
                          (Γ .idx .isEquivalence .refl , WObj .idx .isEquivalence .sym (embed-unembed-id Q j)))) ≈-refl ⟩
            (y .fam .subst (y .idx .isEquivalence .trans
                             (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                               (Γ .idx .isEquivalence .refl , fobj Q WObj .idx .isEquivalence .refl))
                             (alg .idxf .PS._⇒_.func-resp-≈
                               (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q)))))) ∘
               y .fam .subst (h .idxf .PS._⇒_.func-resp-≈
                                (Γ .idx .isEquivalence .refl , WObj .idx .isEquivalence .sym (embed-unembed-id Q j)))) ∘
            h .famf .transf (γ , inF j)
          ≈⟨ assoc _ _ _ ⟩
            y .fam .subst _ ∘
              (y .fam .subst (h .idxf .PS._⇒_.func-resp-≈
                                (Γ .idx .isEquivalence .refl , WObj .idx .isEquivalence .sym (embed-unembed-id Q j))) ∘
               h .famf .transf (γ , inF j))
          ≈˘⟨ ∘-cong ≈-refl (h .famf .natural {γ , inF j} {γ , inF (embed-idx Q (unembed-idx Q j))}
                              (Γ .idx .isEquivalence .refl ,
                               WObj .idx .isEquivalence .sym (embed-unembed-id Q j))) ⟩
            y .fam .subst _ ∘ (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               (Γ ⊗ WObj) .fam .subst
                 (Γ .idx .isEquivalence .refl , WObj .idx .isEquivalence .sym (embed-unembed-id Q j)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left) ≈-refl)) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               pair p₁ (WFam-subst Q (WObj .idx .isEquivalence .sym (embed-unembed-id Q j)) ∘ p₂))
          ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl (pair-cong ≈-refl (∘-cong (embed-unembed-fam-id Q j) ≈-refl))) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               pair p₁ ((embed-fam Q (unembed-idx Q j) ∘ unembed-fam Q j) ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (pair-cong ≈-refl (assoc _ _ _))) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               pair p₁ (embed-fam Q (unembed-idx Q j) ∘ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                (≈-trans (pair-cong (≈-sym id-left) ≈-refl) (≈-sym (pair-compose _ _ _ _)))) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               (prod-m (id _) (embed-fam Q (unembed-idx Q j)) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                (∘-cong (≈-trans (pair-cong id-left ≈-refl) (pair-cong ≈-refl (≈-sym id-left))) ≈-refl)) ⟩
            y .fam .subst _ ∘
              (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
               (pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂)) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
            y .fam .subst _ ∘
              ((h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘ pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈˘⟨ ∘-cong ≈-refl (∘-cong id-left ≈-refl) ⟩
            y .fam .subst _ ∘
              ((id _ ∘
                (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘ pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂)))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ ∘-cong (y .fam .trans*
                       (alg .idxf .PS._⇒_.func-resp-≈
                          (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q)))))
                       (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                          (Γ .idx .isEquivalence .refl , fobj Q WObj .idx .isEquivalence .refl))) ≈-refl ⟩
            (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                              (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q))))) ∘
             y .fam .subst (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                              (Γ .idx .isEquivalence .refl , fobj Q WObj .idx .isEquivalence .refl))) ∘
              ((id _ ∘
                (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘ pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂)))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
            y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                              (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q))))) ∘
              ((y .fam .subst (h-step ._≃_.idxf-eq .PS._≃m_.func-eq
                                 (Γ .idx .isEquivalence .refl , fobj Q WObj .idx .isEquivalence .refl)) ∘
                (id _ ∘
                 (h .famf .transf (γ , inF (embed-idx Q (unembed-idx Q j))) ∘
                  pair p₁ (id _ ∘ (embed-fam Q (unembed-idx Q j) ∘ p₂))))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (∘-cong (h-step ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , unembed-idx Q j}) ≈-refl) ⟩
            y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                              (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q))))) ∘
              ((cat Category.∘ alg) (products .HasProducts.pair (products .HasProducts.p₁) (fmor Q h))
                 .famf .transf (γ , unembed-idx Q j) ∘ pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ ∘-cong ≈-refl (∘-cong id-left ≈-refl) ⟩
            y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                              (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q))))) ∘
              ((alg .famf .transf (γ , fmor Q h .idxf .PS._⇒_.func (γ , unembed-idx Q j)) ∘
                pair p₁ (fmor Q h .famf .transf (γ , unembed-idx Q j))) ∘
               pair p₁ (unembed-fam Q j ∘ p₂))
          ≈⟨ ≈-trans (≈-sym (assoc _ _ _)) (∘-cong (≈-sym (assoc _ _ _)) ≈-refl) ⟩
            ((y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈
                                (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q))))) ∘
              alg .famf .transf (γ , fmor Q h .idxf .PS._⇒_.func (γ , unembed-idx Q j))) ∘
             pair p₁ (fmor Q h .famf .transf (γ , unembed-idx Q j))) ∘
            pair p₁ (unembed-fam Q j ∘ p₂)
          ≈˘⟨ ∘-cong (∘-cong (alg .famf .natural
                                (Γ .idx .isEquivalence .refl ,
                                 η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q))))) ≈-refl) ≈-refl ⟩
            ((alg .famf .transf (γ , project-idx Q γ j) ∘
              (Γ ⊗ fobj Q y) .fam .subst
                (Γ .idx .isEquivalence .refl , η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q))))) ∘
             pair p₁ (fmor Q h .famf .transf (γ , unembed-idx Q j))) ∘
            pair p₁ (unembed-fam Q j ∘ p₂)
          ≈⟨ ∘-cong (∘-cong (∘-cong ≈-refl
                (pair-cong (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left) ≈-refl)) ≈-refl) ≈-refl ⟩
            ((alg .famf .transf (γ , project-idx Q γ j) ∘
              pair p₁ (fobj Q y .fam .subst
                         (η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q)))) ∘ p₂)) ∘
             pair p₁ (fmor Q h .famf .transf (γ , unembed-idx Q j))) ∘
            pair p₁ (unembed-fam Q j ∘ p₂)
          ≈⟨ ≈-trans (assoc _ _ _) (assoc _ _ _) ⟩
            alg .famf .transf (γ , project-idx Q γ j) ∘
              (pair p₁ (fobj Q y .fam .subst
                          (η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q)))) ∘ p₂) ∘
               (pair p₁ (fmor Q h .famf .transf (γ , unembed-idx Q j)) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
                (≈-trans (pair-natural _ _ _) (pair-cong (pair-p₁ _ _) ≈-refl))) ⟩
            alg .famf .transf (γ , project-idx Q γ j) ∘
              (pair p₁ (fobj Q y .fam .subst
                          (η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q)))) ∘ p₂) ∘
               pair p₁ (fmor Q h .famf .transf (γ , unembed-idx Q j) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (≈-trans (pair-natural _ _ _)
                              (≈-trans (pair-cong (pair-p₁ _ _) (assoc _ _ _))
                                              (pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _))))) ⟩
            alg .famf .transf (γ , project-idx Q γ j) ∘
              pair p₁ (fobj Q y .fam .subst
                         (η-idx Q (Γ .idx .isEquivalence .refl) (WIdx-≈-refl (idx-of Q) ((idx-of Q)))) ∘
                       (fmor Q h .famf .transf (γ , unembed-idx Q j) ∘ pair p₁ (unembed-fam Q j ∘ p₂)))
          ≈⟨ ∘-cong ≈-refl (pair-cong ≈-refl (≈-trans (≈-sym (assoc _ _ _)) (η-fam Q γ j))) ⟩
            alg .famf .transf (γ , project-idx Q γ j) ∘ pair p₁ (project-fam Q γ j)
          ∎ where open ≈-Reasoning isEquiv
        η-fam (P Poly.+ R) γ (inj₁ x) =
          ≈-trans
            (∘-cong (∘-cong ≈-refl (≈-trans id-left id-left)) ≈-refl) (η-fam P γ x)
        η-fam (P Poly.+ R) γ (inj₂ z) =
          ≈-trans
            (∘-cong (∘-cong ≈-refl (≈-trans id-left id-left)) ≈-refl) (η-fam R γ z)
        η-fam (P Poly.× R) γ (x , z) = begin
            (prod-m (fobj P y .fam .subst _) (fobj R y .fam .subst _) ∘
             pair (id _ ∘ (fmor P h .famf .transf (γ , unembed-idx P x) ∘ pair p₁ (id _ ∘ (p₁ ∘ p₂))))
                  (id _ ∘ (fmor R h .famf .transf (γ , unembed-idx R z) ∘ pair p₁ (id _ ∘ (p₂ ∘ p₂))))) ∘
             pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
          ≈⟨ ∘-cong (∘-cong ≈-refl
                (pair-cong (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left)))
                           (≈-trans id-left (∘-cong ≈-refl (pair-cong ≈-refl id-left))))) ≈-refl ⟩
            (prod-m (fobj P y .fam .subst _) (fobj R y .fam .subst _) ∘
             pair (fmor P h .famf .transf (γ , unembed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))
                  (fmor R h .famf .transf (γ , unembed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘
            pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
          ≈⟨ ∘-cong (pair-compose _ _ _ _) ≈-refl ⟩
            pair (fobj P y .fam .subst _ ∘ (fmor P h .famf .transf (γ , unembed-idx P x) ∘ pair p₁ (p₁ ∘ p₂)))
                 (fobj R y .fam .subst _ ∘ (fmor R h .famf .transf (γ , unembed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘
            pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
          ≈⟨ pair-natural _ _ _ ⟩
            pair ((fobj P y .fam .subst _ ∘
                     (fmor P h .famf .transf (γ , unembed-idx P x) ∘ pair p₁ (p₁ ∘ p₂))) ∘
                  pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
                 ((fobj R y .fam .subst _ ∘ (fmor R h .famf .transf (γ , unembed-idx R z) ∘ pair p₁ (p₂ ∘ p₂))) ∘
                  pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
          ≈⟨ pair-cong (bridge P x (p₁ ∘ p₂) (p₁ ∘ p₂) merge-pair-P fold-pair-P)
                       (bridge R z (p₂ ∘ p₂) (p₂ ∘ p₂) merge-pair-R fold-pair-R) ⟩
            pair (project-fam P γ x ∘ pair p₁ (p₁ ∘ p₂)) (project-fam R γ z ∘ pair p₁ (p₂ ∘ p₂))
          ∎ where
            merge-pair-P : pair {prod (Γ .fam .fm γ) _} p₁ (p₁ ∘ p₂)
                           ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
                         ≈ pair p₁ (unembed-fam P x ∘ (p₁ ∘ p₂))
            merge-pair-P =
              begin
                pair p₁ (p₁ ∘ p₂) ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
              ≈⟨ pair-natural _ _ _ ⟩
                pair (p₁ ∘ pair p₁ _) ((p₁ ∘ p₂) ∘ pair p₁ _)
              ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
                pair p₁ (p₁ ∘ (p₂ ∘ pair p₁ _))
              ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
                pair p₁ (p₁ ∘ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
              ≈⟨ pair-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
                pair p₁ ((p₁ ∘ prod-m (unembed-fam P x) (unembed-fam R z)) ∘ p₂)
              ≈⟨ pair-cong ≈-refl (∘-cong (pair-p₁ _ _) ≈-refl) ⟩
                pair p₁ ((unembed-fam P x ∘ p₁) ∘ p₂)
              ≈⟨ pair-cong ≈-refl (assoc _ _ _) ⟩
                pair p₁ (unembed-fam P x ∘ (p₁ ∘ p₂))
              ∎ where open ≈-Reasoning isEquiv

            fold-pair-P : pair {prod (Γ .fam .fm γ) (WFam-fm P x)} p₁ (unembed-fam P x ∘ p₂)
                          ∘ pair {prod (Γ .fam .fm γ) (prod (WFam-fm P x) (WFam-fm R z))} p₁ (p₁ ∘ p₂)
                        ≈ pair p₁ (unembed-fam P x ∘ (p₁ ∘ p₂))
            fold-pair-P = begin
                pair p₁ (unembed-fam P x ∘ p₂) ∘ pair p₁ (p₁ ∘ p₂)
              ≈⟨ pair-natural _ _ _ ⟩
                pair (p₁ ∘ pair p₁ _) ((unembed-fam P x ∘ p₂) ∘ pair p₁ _)
              ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
                pair p₁ (unembed-fam P x ∘ (p₂ ∘ pair p₁ _))
              ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
                pair p₁ (unembed-fam P x ∘ (p₁ ∘ p₂))
              ∎ where open ≈-Reasoning isEquiv

            merge-pair-R : pair {prod (Γ .fam .fm γ) _} p₁ (p₂ ∘ p₂) ∘
                           pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
                         ≈ pair p₁ (unembed-fam R z ∘ (p₂ ∘ p₂))
            merge-pair-R = begin
                pair p₁ (p₂ ∘ p₂) ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
              ≈⟨ pair-natural _ _ _ ⟩
                pair (p₁ ∘ pair p₁ _) ((p₂ ∘ p₂) ∘ pair p₁ _)
              ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
                pair p₁ (p₂ ∘ (p₂ ∘ pair p₁ _))
              ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
                pair p₁ (p₂ ∘ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
              ≈⟨ pair-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
                pair p₁ ((p₂ ∘ prod-m (unembed-fam P x) (unembed-fam R z)) ∘ p₂)
              ≈⟨ pair-cong ≈-refl (∘-cong (pair-p₂ _ _) ≈-refl) ⟩
                pair p₁ ((unembed-fam R z ∘ p₂) ∘ p₂)
              ≈⟨ pair-cong ≈-refl (assoc _ _ _) ⟩
                pair p₁ (unembed-fam R z ∘ (p₂ ∘ p₂))
              ∎ where open ≈-Reasoning isEquiv

            fold-pair-R : pair {prod (Γ .fam .fm γ) (WFam-fm R z)} p₁ (unembed-fam R z ∘ p₂)
                          ∘ pair {prod (Γ .fam .fm γ) (prod (WFam-fm P x) (WFam-fm R z))} p₁ (p₂ ∘ p₂)
                        ≈ pair p₁ (unembed-fam R z ∘ (p₂ ∘ p₂))
            fold-pair-R = begin
                pair p₁ (unembed-fam R z ∘ p₂) ∘ pair p₁ (p₂ ∘ p₂)
              ≈⟨ pair-natural _ _ _ ⟩
                pair (p₁ ∘ pair p₁ _) ((unembed-fam R z ∘ p₂) ∘ pair p₁ _)
              ≈⟨ pair-cong (pair-p₁ _ _) (assoc _ _ _) ⟩
                pair p₁ (unembed-fam R z ∘ (p₂ ∘ pair p₁ _))
              ≈⟨ pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
                pair p₁ (unembed-fam R z ∘ (p₂ ∘ p₂))
              ∎ where open ≈-Reasoning isEquiv

            bridge : (W : Poly cat) (j : WIdx (idx-of Q) (idx-of W))
                     (π-poly : prod (Γ .fam .fm γ)
                                    (prod (fobj P WObj .fam .fm (unembed-idx P x))
                                          (fobj R WObj .fam .fm (unembed-idx R z)))
                               ⇒ fobj W WObj .fam .fm (unembed-idx W j))
                     (π-WFam : prod (Γ .fam .fm γ) (prod (WFam-fm P x) (WFam-fm R z)) ⇒ WFam-fm W j)
                     (merge : pair p₁ π-poly ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
                              ≈ pair p₁ (unembed-fam W j ∘ π-WFam))
                     (fold : pair p₁ (unembed-fam W j ∘ p₂) ∘ pair p₁ π-WFam
                             ≈ pair p₁ (unembed-fam W j ∘ π-WFam)) →
                     (fobj W y .fam .subst _ ∘
                       (fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ π-poly)) ∘
                     pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
                   ≈ project-fam W γ j ∘ pair p₁ π-WFam
            bridge W j π-poly π-WFam merge fold = begin
                (fobj W y .fam .subst _ ∘
                   (fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ π-poly)) ∘
                pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)
              ≈⟨ assoc _ _ _ ⟩
                fobj W y .fam .subst _ ∘
                  ((fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ π-poly) ∘
                   pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂))
              ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
                fobj W y .fam .subst _ ∘
                  (fmor W h .famf .transf (γ , unembed-idx W j) ∘
                   (pair p₁ π-poly ∘ pair p₁ (prod-m (unembed-fam P x) (unembed-fam R z) ∘ p₂)))
              ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl merge) ⟩
                fobj W y .fam .subst _ ∘
                  (fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ (unembed-fam W j ∘ π-WFam))
              ≈˘⟨ ∘-cong ≈-refl (∘-cong ≈-refl fold) ⟩
                fobj W y .fam .subst _ ∘
                  (fmor W h .famf .transf (γ , unembed-idx W j) ∘
                   (pair p₁ (unembed-fam W j ∘ p₂) ∘ pair p₁ π-WFam))
              ≈˘⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
                fobj W y .fam .subst _ ∘
                  ((fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ (unembed-fam W j ∘ p₂)) ∘
                   pair p₁ π-WFam)
              ≈˘⟨ assoc _ _ _ ⟩
                (fobj W y .fam .subst _ ∘
                   (fmor W h .famf .transf (γ , unembed-idx W j) ∘ pair p₁ (unembed-fam W j ∘ p₂))) ∘
                pair p₁ π-WFam
              ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
                ((fobj W y .fam .subst _ ∘
                    fmor W h .famf .transf (γ , unembed-idx W j)) ∘ pair p₁ (unembed-fam W j ∘ p₂)) ∘
                pair p₁ π-WFam
              ≈⟨ ∘-cong (η-fam W γ j) ≈-refl ⟩
                project-fam W γ j ∘ pair p₁ π-WFam
              ∎ where open ≈-Reasoning isEquiv

            open ≈-Reasoning isEquiv

  hasMu : HasMu
  hasMu .HasMu.μ Q          = W-types.WObj Q
  hasMu .HasMu.inF Q        = W-types.inF-mor Q
  hasMu .HasMu.⦅_⦆ {Γ} {Q}  = W-types.Fold.fold Q
  hasMu .HasMu.⦅⦆-β {Γ} {Q} alg ._≃_.idxf-eq .PS._≃m_.func-eq {γ₁ , i₁} {γ₂ , i₂} (γ₁≈γ₂ , i₁≈i₂) =
    alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , β-idx Q γ₁≈γ₂ i₁≈i₂)
    where open W-types Q; open Fold alg
  hasMu .HasMu.⦅⦆-β {Γ} {Q} {y} alg ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , i} = begin
      y .fam .subst _ ∘ (id _ ∘ (alg .famf .transf (γ , project-idx Q γ (embed-idx Q i)) ∘
          pair p₁ (project-fam Q γ (embed-idx Q i)) ∘ pair p₁ (id _ ∘ (embed-fam Q i ∘ p₂))))
    ≈⟨ ∘-cong ≈-refl id-left ⟩
      y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx Q γ (embed-idx Q i)) ∘
          pair p₁ (project-fam Q γ (embed-idx Q i)) ∘ pair p₁ (id _ ∘ (embed-fam Q i ∘ p₂)))
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx Q γ (embed-idx Q i)) ∘
          (pair p₁ (project-fam Q γ (embed-idx Q i)) ∘ pair p₁ (id _ ∘ (embed-fam Q i ∘ p₂))))
    ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl
        (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _) (∘-cong ≈-refl (pair-cong ≈-refl id-left))))) ⟩
      y .fam .subst _ ∘ (alg .famf .transf (γ , project-idx Q γ (embed-idx Q i)) ∘
          pair p₁ (project-fam Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂)))
    ≈⟨ ≈-sym (assoc _ _ _) ⟩
      (y .fam .subst _ ∘ alg .famf .transf (γ , project-idx Q γ (embed-idx Q i))) ∘
          pair p₁ (project-fam Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂))
    ≈⟨ ∘-cong
        (≈-sym (alg .famf .natural (
          Setoid.isEquivalence (Γ .idx) .IsEquivalence.refl ,
          β-idx Q (Setoid.isEquivalence (Γ .idx) .IsEquivalence.refl)
                  (Setoid.isEquivalence (fobj Q WObj .idx) .IsEquivalence.refl)
        ))) ≈-refl ⟩
      (alg .famf .transf (γ , fmor Q fold .idxf .PS._⇒_.func (γ , i)) ∘
          pair (Γ .fam .subst _ ∘ p₁) (fobj Q y .fam .subst _ ∘ p₂)) ∘
          pair p₁ (project-fam Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂))
    ≈⟨ assoc _ _ _ ⟩
      alg .famf .transf (γ , fmor Q fold .idxf .PS._⇒_.func (γ , i)) ∘
          (pair (Γ .fam .subst _ ∘ p₁) (fobj Q y .fam .subst _ ∘ p₂) ∘
          pair p₁ (project-fam Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂)))
    ≈⟨ ∘-cong ≈-refl (pair-compose _ _ _ _) ⟩
      alg .famf .transf (γ , fmor Q fold .idxf .PS._⇒_.func (γ , i)) ∘
          pair (Γ .fam .subst _ ∘ p₁)
               (fobj Q y .fam .subst _ ∘ (project-fam Q γ (embed-idx Q i) ∘ pair p₁ (embed-fam Q i ∘ p₂)))
    ≈⟨ ∘-cong ≈-refl (pair-cong
                (≈-trans (∘-cong (Γ .fam .refl*) ≈-refl) id-left) (≈-trans (≈-sym (assoc _ _ _)) (β-fam Q γ i))) ⟩
      alg .famf .transf (γ , fmor Q fold .idxf .PS._⇒_.func (γ , i)) ∘
          pair p₁ (fmor Q fold .famf .transf (γ , i))
    ≈⟨ ≈-sym id-left ⟩
      id _ ∘ (alg .famf .transf (γ , fmor Q fold .idxf .PS._⇒_.func (γ , i)) ∘
          pair p₁ (fmor Q fold .famf .transf (γ , i)))
    ∎ where
      open W-types Q; open Fold alg; open ≈-Reasoning isEquiv
  hasMu .HasMu.⦅⦆-η {Γ} {Q} {y} alg h h-step ._≃_.idxf-eq .PS._≃m_.func-eq {γ₁ , inF i₁} {γ₂ , inF i₂} (γ₁≈γ₂ , t₁≈t₂) =
    η-idx h h-step Poly.var γ₁≈γ₂ {inF i₁} {inF i₂} t₁≈t₂
    where open W-types Q; open Fold alg
  hasMu .HasMu.⦅⦆-η {Γ} {Q} {y} alg h h-step ._≃_.famf-eq .indexed-family._≃f_.transf-eq {γ , inF i} =
    ≈-trans
      (≈-trans (≈-sym id-right)
                      (≈-sym (∘-cong ≈-refl (≈-trans (pair-cong ≈-refl id-left) pair-ext0))))
      (η-fam h h-step Poly.var γ (inF i))
    where open W-types Q; open Fold alg
