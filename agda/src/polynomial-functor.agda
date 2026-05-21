{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_; suc; lift)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import prop using (_,_; tt)
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; cong₂)
open import categories
  using (Category; HasTerminal; HasProducts; HasCoproducts; HasStrongCoproducts; strong-coproducts→coproducts)
open import functor using (Functor; Id; StrongPointedFunctor; StrongPointedFunctor-Id)
open import prop-setoid as PS
  using (IsEquivalence; Setoid; module ≈-Reasoning)
open import indexed-family using (Fam; _⇒f_; changeCat)
import fam
import fam-functor

-- Rename Setoid._≈_ to _≈s_ to avoid clashing with Category._≈_ (morphism eq).
open Setoid using (Carrier) renaming (_≈_ to _≈s_)

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

-- Map a polynomial through a functor by applying F to const slots.
Poly-map : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} →
           Functor 𝒞 𝒟 → Poly 𝒞 → Poly 𝒟
Poly-map F one         = one
Poly-map F (const A)   = const (Functor.fobj F A)
Poly-map F var         = var
Poly-map F (P₁ + P₂)   = Poly-map F P₁ + Poly-map F P₂
Poly-map F (P₁ × P₂)   = Poly-map F P₁ × Poly-map F P₂

------------------------------------------------------------------------------
-- Polynomial signature extended with a Mon constructor (fibre-only decoration relative to whatever LiftMon
-- the interpretation supplies).
data μPoly {o m e} (𝒞 : Category o m e) : Set o where
  one    : μPoly 𝒞
  const  : Category.obj 𝒞 → μPoly 𝒞
  var    : μPoly 𝒞
  _+_    : μPoly 𝒞 → μPoly 𝒞 → μPoly 𝒞
  _×_    : μPoly 𝒞 → μPoly 𝒞 → μPoly 𝒞
  Mon    : μPoly 𝒞 → μPoly 𝒞

module Sem {o m e} {𝒞 : Category o m e}
           (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (SCP : HasStrongCoproducts 𝒞 P) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  CP : HasCoproducts 𝒞
  CP = strong-coproducts→coproducts T SCP
  open HasCoproducts CP
  open HasStrongCoproducts SCP using () renaming (copair to scopair)

  poly-obj : Poly 𝒞 → obj → obj
  poly-obj one         _ = terminal
  poly-obj (const A)   _ = A
  poly-obj var         x = x
  poly-obj (P + Q)     x = coprod (poly-obj P x) (poly-obj Q x)
  poly-obj (P × Q)     x = prod   (poly-obj P x) (poly-obj Q x)

  -- Open-form functorial action of Poly Q: lifts (prod Γ X ⇒ Y) to
  -- (prod Γ (poly-obj Q X) ⇒ poly-obj Q Y). Uses strong copair for sums.
  poly-fmor : ∀ Q {Γ X Y} → (prod Γ X ⇒ Y) → (prod Γ (poly-obj Q X) ⇒ poly-obj Q Y)
  poly-fmor one         _ = to-terminal
  poly-fmor (const A)   _ = p₂
  poly-fmor var         h = h
  poly-fmor (Q₁ + Q₂)   h = scopair (in₁ ∘ poly-fmor Q₁ h) (in₂ ∘ poly-fmor Q₂ h)
  poly-fmor (Q₁ × Q₂)   h = pair (poly-fmor Q₁ h ∘ pair p₁ (p₁ ∘ p₂))
                                  (poly-fmor Q₂ h ∘ pair p₁ (p₂ ∘ p₂))

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
      -- Open (parametric) form: algebra in extended context. Avoids the
      -- closure conversion that would otherwise need exponentials.
      ⦅_⦆  : ∀ {Γ Q y} → (prod Γ (poly-obj Q y) ⇒ y) → prod Γ (μ Q) ⇒ y

      -- β: ⦅alg⦆ on a rolled value (in extended context) equals alg applied
      -- to the recursively folded structure (γ threaded through).
      ⦅⦆-β : ∀ {Γ Q y} (alg : prod Γ (poly-obj Q y) ⇒ y) →
             (⦅ alg ⦆ ∘ pair p₁ (inF Q ∘ p₂)) ≈ (alg ∘ pair p₁ (poly-fmor Q ⦅ alg ⦆))
      -- η: ⦅alg⦆ is the unique morphism satisfying β.
      ⦅⦆-η : ∀ {Γ Q y} (alg : prod Γ (poly-obj Q y) ⇒ y) (h : prod Γ (μ Q) ⇒ y) →
             (h ∘ pair p₁ (inF Q ∘ p₂)) ≈ (alg ∘ pair p₁ (poly-fmor Q h)) →
             h ≈ ⦅ alg ⦆

  -- Interpretation of μPoly as a functor in 𝒞, plus the corresponding HasMu interface, where F interprets Mon.
  module μPoly-Sem (F : Functor 𝒞 𝒞) where
    μPoly-obj : μPoly 𝒞 → obj → obj
    μPoly-obj one        _ = terminal
    μPoly-obj (const A)  _ = A
    μPoly-obj var        x = x
    μPoly-obj (P + Q)    x = coprod (μPoly-obj P x) (μPoly-obj Q x)
    μPoly-obj (P × Q)    x = prod   (μPoly-obj P x) (μPoly-obj Q x)
    μPoly-obj (Mon P)    x = Functor.fobj F (μPoly-obj P x)

    record HasMu-μPoly : Set (o ⊔ m ⊔ e) where
      field
        μ    : μPoly 𝒞 → obj
        inμ  : ∀ Q → μPoly-obj Q (μ Q) ⇒ μ Q
        -- Open (parametric) form: algebra in extended context. Avoids the
        -- closure conversion that would otherwise need exponentials.
        ⦅_⦆  : ∀ {Γ Q y} → (prod Γ (μPoly-obj Q y) ⇒ y) → prod Γ (μ Q) ⇒ y
      -- FIXME: equations (β/η for inμ / ⦅_⦆). Mon case needs strength on F.

------------------------------------------------------------------------------
-- A functor F : 𝒞 → 𝒟 preserves μ if, for each polynomial signature P, the
-- F-image of 𝒞's μ P is isomorphic to 𝒟's μ of the F-mapped polynomial.
module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂}
         (T₁ : HasTerminal 𝒞) (P₁ : HasProducts 𝒞) (SCP₁ : HasStrongCoproducts 𝒞 P₁)
         (T₂ : HasTerminal 𝒟) (P₂ : HasProducts 𝒟) (SCP₂ : HasStrongCoproducts 𝒟 P₂)
         where
  private
    module S₁ = Sem T₁ P₁ SCP₁
    module S₂ = Sem T₂ P₂ SCP₂

  Preserves-μ : S₁.HasMu → S₂.HasMu → Functor 𝒞 𝒟 → Set _
  Preserves-μ 𝒞Mu 𝒟Mu F =
    ∀ (P : Poly 𝒞) →
      Category.Iso 𝒟 (Functor.fobj F (S₁.HasMu.μ 𝒞Mu P))
                      (S₂.HasMu.μ 𝒟Mu (Poly-map F P))

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
    WIdx P (param A)   = Carrier A
    WIdx P var         = W P
    WIdx P (Q₁ + Q₂)   = WIdx P Q₁ ⊎ WIdx P Q₂
    WIdx P (Q₁ × Q₂)   = WIdx P Q₁ ×T WIdx P Q₂

  mutual
    W-≈ : (P : IdxPoly) → W P → W P → Prop e
    W-≈ P (inF i₁) (inF i₂) = WIdx-≈ P P i₁ i₂

    WIdx-≈ : (P Q : IdxPoly) → WIdx P Q → WIdx P Q → Prop e
    WIdx-≈ P one         _          _          = ⊤
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
    WIdx-≈-refl P one                   = tt
    WIdx-≈-refl P (param A) {x}         = IsEquivalence.refl (Setoid.isEquivalence A) {x}
    WIdx-≈-refl P var       {w}         = W-≈-refl P {w}
    WIdx-≈-refl P (Q₁ + Q₂) {inj₁ x}    = WIdx-≈-refl P Q₁ {x}
    WIdx-≈-refl P (Q₁ + Q₂) {inj₂ y}    = WIdx-≈-refl P Q₂ {y}
    WIdx-≈-refl P (Q₁ × Q₂) {x , y}     = WIdx-≈-refl P Q₁ {x} , WIdx-≈-refl P Q₂ {y}

  mutual
    W-≈-sym : ∀ P {w₁ w₂} → W-≈ P w₁ w₂ → W-≈ P w₂ w₁
    W-≈-sym P {inF i₁} {inF i₂} i₁≈i₂ = WIdx-≈-sym P P {i₁} {i₂} i₁≈i₂

    WIdx-≈-sym : ∀ P Q {x y} → WIdx-≈ P Q x y → WIdx-≈ P Q y x
    WIdx-≈-sym P one         _  = tt
    WIdx-≈-sym P (param A) {x} {y} x≈y = IsEquivalence.sym (Setoid.isEquivalence A) x≈y
    WIdx-≈-sym P var       {w₁} {w₂} w₁≈w₂ = W-≈-sym P {w₁} {w₂} w₁≈w₂
    WIdx-≈-sym P (Q₁ + Q₂) {inj₁ x₁} {inj₁ x₂} x₁≈x₂ = WIdx-≈-sym P Q₁ x₁≈x₂
    WIdx-≈-sym P (Q₁ + Q₂) {inj₂ y₁} {inj₂ y₂} y₁≈y₂ = WIdx-≈-sym P Q₂ y₁≈y₂
    WIdx-≈-sym P (Q₁ × Q₂) {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = WIdx-≈-sym P Q₁ x₁≈x₂ , WIdx-≈-sym P Q₂ y₁≈y₂

  mutual
    W-≈-trans : ∀ P {w₁ w₂ w₃} → W-≈ P w₁ w₂ → W-≈ P w₂ w₃ → W-≈ P w₁ w₃
    W-≈-trans P {inF _} {inF _} {inF _} w₁≈w₂ w₂≈w₃ = WIdx-≈-trans P P w₁≈w₂ w₂≈w₃

    WIdx-≈-trans : ∀ P Q {x y z} →
                      WIdx-≈ P Q x y → WIdx-≈ P Q y z → WIdx-≈ P Q x z
    WIdx-≈-trans P one        _  _  = tt
    WIdx-≈-trans P (param A) {x} {y} {z} x≈y y≈z = IsEquivalence.trans (Setoid.isEquivalence A) x≈y y≈z
    WIdx-≈-trans P var       {x} {y} {z} x≈y y≈z = W-≈-trans P {x} {y} {z} x≈y y≈z
    WIdx-≈-trans P (Q₁ + Q₂) {inj₁ _} {inj₁ _} {inj₁ _} x≈y y≈z = WIdx-≈-trans P Q₁ x≈y y≈z
    WIdx-≈-trans P (Q₁ + Q₂) {inj₂ _} {inj₂ _} {inj₂ _} x≈y y≈z = WIdx-≈-trans P Q₂ x≈y y≈z
    WIdx-≈-trans P (Q₁ × Q₂) {_ , _} {_ , _} {_ , _} (x₁≈y₁ , x₂≈y₂) (y₁≈z₁ , y₂≈z₂) =
      WIdx-≈-trans P Q₁ x₁≈y₁ y₁≈z₁ , WIdx-≈-trans P Q₂ x₂≈y₂ y₂≈z₂

  WSetoid : IdxPoly → Setoid o e
  WSetoid P .Carrier                            = W P
  WSetoid P ._≈s_                                = W-≈ P
  WSetoid P .Setoid.isEquivalence .IsEquivalence.refl  {w} = W-≈-refl P {w}
  WSetoid P .Setoid.isEquivalence .IsEquivalence.sym   {w₁} {w₂} = W-≈-sym P {w₁} {w₂}
  WSetoid P .Setoid.isEquivalence .IsEquivalence.trans {w₁} {w₂} {w₃} = W-≈-trans P {w₁} {w₂} {w₃}

------------------------------------------------------------------------------
-- Subset of Lucatelli Nunes & Vákár's μν Poly_L (Def 53). `Mon` decorates a
-- sub-polynomial with the ambient fibre-level lifting monad, fibre-only.
module Mu {o m e os es} {𝒟 : Category o m e}
          (T : HasTerminal 𝒟) (PP : HasProducts 𝒟) (L : StrongPointedFunctor PP) where
  open fam.CategoryOfFamilies os es 𝒟
  open Obj
  open products PP
  open StrongPointedFunctor L using (F)   -- L's underlying Functor 𝒟 𝒟

  idx-of : μPoly cat → IdxPoly {os} {es}
  idx-of one          = IdxPoly.one
  idx-of (const A)    = IdxPoly.param (A .idx)
  idx-of var          = IdxPoly.var
  idx-of (F + G)      = idx-of F IdxPoly.+ idx-of G
  idx-of (F × G)      = idx-of F IdxPoly.× idx-of G
  idx-of (Mon F)      = idx-of F

  open HasTerminal (terminal T) using () renaming (witness to Fam-terminal)
  open HasCoproducts coproducts using () renaming (coprod to Fam-coprod)

  -- Fibre-wise lift of L's endofunctor to Fam(𝒟). Idx preserved; each fibre wrapped.
  Mon-Fam : Obj → Obj
  Mon-Fam Y .idx = Y .idx
  Mon-Fam Y .fam = changeCat F (Y .fam)

  μPoly-obj : μPoly cat → Obj → Obj
  μPoly-obj one        X = Fam-terminal
  μPoly-obj (const A)  X = A
  μPoly-obj var        X = X
  μPoly-obj (F + G)    X = Fam-coprod (μPoly-obj F X) (μPoly-obj G X)
  μPoly-obj (F × G)    X = (μPoly-obj F X) ⊗ (μPoly-obj G X)
  μPoly-obj (Mon F)    X = Mon-Fam (μPoly-obj F X)

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
  open Sem (terminal T) products strongCoproducts

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

    embed-idx : (P : Poly cat) → poly-obj P WObj .idx .Carrier → WIdx poly (idx-of P)
    embed-idx Poly.one         (lift tt)  = lift tt
    embed-idx (Poly.const A)   a          = a
    embed-idx Poly.var         w          = w
    embed-idx (P Poly.+ Q)     (inj₁ x)   = inj₁ (embed-idx P x)
    embed-idx (P Poly.+ Q)     (inj₂ y)   = inj₂ (embed-idx Q y)
    embed-idx (P Poly.× Q)     (x , y)    = (embed-idx P x , embed-idx Q y)

    embed-≈ : (P : Poly cat) → ∀ {x y} →
              poly-obj P WObj .idx ._≈s_ x y → WIdx-≈ poly (idx-of P) (embed-idx P x) (embed-idx P y)
    embed-≈ Poly.one         _   = tt
    embed-≈ (Poly.const A)   eq  = eq
    embed-≈ Poly.var         eq  = eq
    embed-≈ (P Poly.+ Q) {inj₁ _} {inj₁ _} eq        = embed-≈ P eq
    embed-≈ (P Poly.+ Q) {inj₂ _} {inj₂ _} eq        = embed-≈ Q eq
    embed-≈ (P Poly.× Q) {_ , _} {_ , _} (e₁ , e₂)   = (embed-≈ P e₁ , embed-≈ Q e₂)

    embed-fam : (P : Poly cat) (i : poly-obj P WObj .idx .Carrier) →
                poly-obj P WObj .fam .fm i ⇒ WFam-fm P (embed-idx P i)
    embed-fam Poly.one         (lift tt)  = id _
    embed-fam (Poly.const A)   a          = id _
    embed-fam Poly.var         (inF _)    = id _
    embed-fam (P Poly.+ Q)     (inj₁ x)   = embed-fam P x
    embed-fam (P Poly.+ Q)     (inj₂ y)   = embed-fam Q y
    embed-fam (P Poly.× Q)     (x , y)    = prod-m (embed-fam P x) (embed-fam Q y)

    embed-fam-natural : (P : Poly cat) → ∀ {x₁ x₂} (e : poly-obj P WObj .idx ._≈s_ x₁ x₂) →
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

      project-idx : (P : Poly cat) → WIdx poly (idx-of P) → poly-obj P y .idx .Carrier
      project-idx Poly.one       _         = lift tt
      project-idx (Poly.const A) a         = a
      project-idx Poly.var       (inF i)   = alg .idxf .PS._⇒_.func (project-idx Q i)
      project-idx (P Poly.+ Q)   (inj₁ x)  = inj₁ (project-idx P x)
      project-idx (P Poly.+ Q)   (inj₂ z)  = inj₂ (project-idx Q z)
      project-idx (P Poly.× Q)   (x , z)   = (project-idx P x , project-idx Q z)

      project-≈ : (P : Poly cat) → ∀ {x z} → WIdx-≈ poly (idx-of P) x z →
                  poly-obj P y .idx ._≈s_ (project-idx P x) (project-idx P z)
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

    -- Open (parametric) fold: takes algebra in extended context Γ ⊗ poly-obj Q y ⇒ y
    -- and produces Γ ⊗ μ Q ⇒ y. Threads γ through the structural recursion.
    module Open {Γ y : Obj} (alg : Mor (Γ ⊗ poly-obj Q y) y) where
      open Obj
      open Mor

      project-idx-open : (P : Poly cat) → Γ .idx .Carrier → WIdx poly (idx-of P) →
                         poly-obj P y .idx .Carrier
      project-idx-open Poly.one       _ _         = lift tt
      project-idx-open (Poly.const A) _ a         = a
      project-idx-open Poly.var       γ (inF i)   =
        alg .idxf .PS._⇒_.func (γ , project-idx-open Q γ i)
      project-idx-open (P Poly.+ R)   γ (inj₁ x)  = inj₁ (project-idx-open P γ x)
      project-idx-open (P Poly.+ R)   γ (inj₂ z)  = inj₂ (project-idx-open R γ z)
      project-idx-open (P Poly.× R)   γ (x , z)   = (project-idx-open P γ x , project-idx-open R γ z)

      project-≈-open : (P : Poly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
                       (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂) (i₁≈i₂ : WIdx-≈ poly (idx-of P) x z) →
                       poly-obj P y .idx ._≈s_
                         (project-idx-open P γ₁ x) (project-idx-open P γ₂ z)
      project-≈-open Poly.one _ _ = tt
      project-≈-open (Poly.const A) _ eq = eq
      project-≈-open Poly.var {γ₁} {γ₂} {inF _} {inF _} γ₁≈γ₂ eq =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ eq)
      project-≈-open (P Poly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ eq = project-≈-open P γ₁≈γ₂ eq
      project-≈-open (P Poly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ eq = project-≈-open R γ₁≈γ₂ eq
      project-≈-open (P Poly.× R) {x = _ , _} {_ , _} γ₁≈γ₂ (e , f) =
        project-≈-open P γ₁≈γ₂ e , project-≈-open R γ₁≈γ₂ f

      project-fam-open : (P : Poly cat) (γ : Γ .idx .Carrier)
                         (i : WIdx poly (idx-of P)) →
                         prod (Γ .fam .fm γ) (WFam-fm P i) ⇒
                         poly-obj P y .fam .fm (project-idx-open P γ i)
      project-fam-open Poly.one         _ _         = HasTerminal.to-terminal T
      project-fam-open (Poly.const A)   _ _         = p₂
      project-fam-open Poly.var         γ (inF i)   =
        alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i)
      project-fam-open (P Poly.+ R)     γ (inj₁ x)  = project-fam-open P γ x
      project-fam-open (P Poly.+ R)     γ (inj₂ z)  = project-fam-open R γ z
      project-fam-open (P Poly.× R)     γ (x , z)   =
        pair (project-fam-open P γ x ∘ pair p₁ (p₁ ∘ p₂))
             (project-fam-open R γ z ∘ pair p₁ (p₂ ∘ p₂))

      project-fam-natural-open :
        (P : Poly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
        (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂)
        (i₁≈i₂ : WIdx-≈ poly (idx-of P) x z) →
        (project-fam-open P γ₂ z ∘
          prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂)) ≈
        (poly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂) ∘ project-fam-open P γ₁ x)
      project-fam-natural-open Poly.one _ _ =
        HasTerminal.to-terminal-unique T _ _
      project-fam-natural-open (Poly.const A) {x = a} {z = b} _ i₁≈i₂ =
        begin
          p₂ ∘ prod-m _ (A .fam .subst i₁≈i₂)
        ≈⟨ pair-p₂ _ _ ⟩
          A .fam .subst i₁≈i₂ ∘ p₂
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open Poly.var {γ₁} {γ₂} {inF i₁} {inF i₂} γ₁≈γ₂ i₁≈i₂ =
        begin
          (alg .famf .transf (γ₂ , _) ∘ pair p₁ (project-fam-open Q γ₂ i₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂)
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (γ₂ , _) ∘
            (pair p₁ (project-fam-open Q γ₂ i₂) ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂))
        ≈⟨ ∘-cong (isEquiv .refl) (pair-natural _ _ _) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (p₁ ∘ prod-m _ _) (project-fam-open Q γ₂ i₂ ∘ prod-m _ _)
        ≈⟨ ∘-cong (isEquiv .refl)
             (pair-cong (pair-p₁ _ _) (project-fam-natural-open Q γ₁≈γ₂ i₁≈i₂)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁)
                 (poly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂) ∘ project-fam-open Q γ₁ i₁)
        ≈⟨ ≈-sym (∘-cong (isEquiv .refl) (pair-compose _ _ _ _)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            (prod-m (Γ .fam .subst γ₁≈γ₂) (poly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂))
              ∘ pair p₁ (project-fam-open Q γ₁ i₁))
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (γ₂ , _) ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (poly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂)))
            ∘ pair p₁ (project-fam-open Q γ₁ i₁)
        ≈⟨ ∘-cong (alg .famf .natural (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)) (isEquiv .refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂))
            ∘ alg .famf .transf (γ₁ , _))
            ∘ pair p₁ (project-fam-open Q γ₁ i₁)
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂))
            ∘ (alg .famf .transf (γ₁ , _) ∘ pair p₁ (project-fam-open Q γ₁ i₁))
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open (P Poly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural-open P γ₁≈γ₂ i₁≈i₂
      project-fam-natural-open (P Poly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural-open R γ₁≈γ₂ i₁≈i₂
      project-fam-natural-open (P Poly.× R) {γ₁} {γ₂} {x₁ , z₁} {x₂ , z₂} γ₁≈γ₂ (eP , eR) =
        begin
          pair (project-fam-open P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂))
               (project-fam-open R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (prod-m (WFam-subst P eP) (WFam-subst R eR))
        ≈⟨ pair-natural _ _ _ ⟩
          pair ((project-fam-open P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂)) ∘ prod-m _ _)
               ((project-fam-open R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂)) ∘ prod-m _ _)
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (project-fam-open P γ₂ x₂ ∘ (pair p₁ (p₁ ∘ p₂) ∘ prod-m _ _))
               (project-fam-open R γ₂ z₂ ∘ (pair p₁ (p₂ ∘ p₂) ∘ prod-m _ _))
        ≈⟨ pair-cong
             (∘-cong (isEquiv .refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (isEquiv .refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₁ _ _) (isEquiv .refl))
                                  (assoc _ _ _))))))))
             (∘-cong (isEquiv .refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (isEquiv .refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₂ _ _) (isEquiv .refl))
                                  (assoc _ _ _)))))))) ⟩
          pair (project-fam-open P γ₂ x₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst P eP ∘ (p₁ ∘ p₂)))
               (project-fam-open R γ₂ z₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst R eR ∘ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (∘-cong (isEquiv .refl) (≈-sym (pair-compose _ _ _ _)))
                     (∘-cong (isEquiv .refl) (≈-sym (pair-compose _ _ _ _))) ⟩
          pair (project-fam-open P γ₂ x₂ ∘
                 (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P eP) ∘ pair p₁ (p₁ ∘ p₂)))
               (project-fam-open R γ₂ z₂ ∘
                 (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst R eR) ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
          pair ((project-fam-open P γ₂ x₂ ∘ prod-m _ _) ∘ pair p₁ (p₁ ∘ p₂))
               ((project-fam-open R γ₂ z₂ ∘ prod-m _ _) ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (∘-cong (project-fam-natural-open P γ₁≈γ₂ eP) (isEquiv .refl))
                     (∘-cong (project-fam-natural-open R γ₁≈γ₂ eR) (isEquiv .refl)) ⟩
          pair ((poly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ eP) ∘ project-fam-open P γ₁ x₁)
                  ∘ pair p₁ (p₁ ∘ p₂))
               ((poly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ eR) ∘ project-fam-open R γ₁ z₁)
                  ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (poly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ eP)
                 ∘ (project-fam-open P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂)))
               (poly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ eR)
                 ∘ (project-fam-open R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ ≈-sym (pair-compose _ _ _ _) ⟩
          prod-m (poly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ eP))
                 (poly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ eR))
            ∘ pair (project-fam-open P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂))
                   (project-fam-open R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂))
        ∎ where open ≈-Reasoning isEquiv

      fold-open : Mor (Γ ⊗ WObj) y
      fold-open .idxf .PS._⇒_.func (γ , inF i) =
        alg .idxf .PS._⇒_.func (γ , project-idx-open Q γ i)
      fold-open .idxf .PS._⇒_.func-resp-≈ {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)
      fold-open .famf .transf (γ , inF i) =
        alg .famf .transf (γ , project-idx-open Q γ i) ∘
          pair p₁ (project-fam-open Q γ i)
      fold-open .famf .natural {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        project-fam-natural-open Poly.var γ₁≈γ₂ i₁≈i₂

      -- β-idx: project-idx-open through embed-idx agrees with poly-fmor's idx
      -- action of fold-open. Used to prove the β law for ⦅_⦆.
      β-idx : (P : Poly cat)
              {γ₁ γ₂ : Γ .idx .Carrier} (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂)
              {i₁ i₂ : poly-obj P WObj .idx .Carrier}
              (i₁≈i₂ : poly-obj P WObj .idx ._≈s_ i₁ i₂) →
              poly-obj P y .idx ._≈s_
                (project-idx-open P γ₁ (embed-idx P i₁)) (poly-fmor P fold-open .idxf .PS._⇒_.func (γ₂ , i₂))
      β-idx Poly.one       γ₁≈γ₂ i₁≈i₂                                    = tt
      β-idx (Poly.const A) γ₁≈γ₂ i₁≈i₂                                    = {!!}
      β-idx Poly.var       γ₁≈γ₂ {inF i₁} {inF i₂} i₁≈i₂                  = {!!}
      β-idx (P Poly.+ R)   γ₁≈γ₂ {inj₁ x₁} {inj₁ x₂} i₁≈i₂                = {!!}
      β-idx (P Poly.+ R)   γ₁≈γ₂ {inj₂ y₁} {inj₂ y₂} i₁≈i₂                = {!!}
      β-idx (P Poly.× R)   γ₁≈γ₂ {x₁ , z₁} {x₂ , z₂} (eP , eR)         = {!!}

  hasMu : HasMu
  hasMu .HasMu.μ Q          = W-types.WObj Q
  hasMu .HasMu.inF Q        = W-types.inF-mor Q
  hasMu .HasMu.⦅_⦆ {Γ} {Q}  = W-types.Open.fold-open Q
  -- β law for fold-open: by structural induction on the polynomial.
  -- Pointwise both sides apply alg to (γ, X) where X is the result of
  -- recursive folding; the two ways of computing X (via project-idx-open or
  -- via poly-fmor) agree definitionally on each Poly constructor.
  hasMu .HasMu.⦅⦆-β alg ._≃_.idxf-eq = {!!}
  hasMu .HasMu.⦅⦆-β alg ._≃_.famf-eq = {!!}
  hasMu .HasMu.⦅⦆-η alg h x = {!!}

------------------------------------------------------------------------------
-- HasMu-μPoly instance for the Fam construction. Same shape as WFam, with a
-- Mon case at each clause: idx is unchanged, fibre is L.F applied.
module WFam-μ {o m e} (os es : _) {𝒟 : Category o m e}
              (T : HasTerminal 𝒟) (P : HasProducts 𝒟) (L : StrongPointedFunctor P) where
  open Category 𝒟
  open IsEquivalence
  open HasTerminal
  open HasProducts P
  open fam.CategoryOfFamilies os es 𝒟
  open products P  -- Fam-level products
  open _⇒f_
  open Sem (terminal T) products strongCoproducts
  open StrongPointedFunctor L
  open μPoly-Sem (fam-functor.FamF os es F)

  module W-types-μ (Q : μPoly cat) where
    open Obj
    open Mor
    open Fam

    idx-of-μ : μPoly cat → IdxPoly
    idx-of-μ μPoly.one        = one
    idx-of-μ (μPoly.const A)  = param (A .idx)
    idx-of-μ μPoly.var        = var
    idx-of-μ (P μPoly.+ Q)    = idx-of-μ P + idx-of-μ Q
    idx-of-μ (P μPoly.× Q)    = idx-of-μ P × idx-of-μ Q
    idx-of-μ (μPoly.Mon P)    = idx-of-μ P   -- Mon doesn't change idx

    poly : IdxPoly
    poly = idx-of-μ Q

    WFam-fm : (P : μPoly cat) → WIdx poly (idx-of-μ P) → obj
    WFam-fm μPoly.one          _        = T .witness
    WFam-fm (μPoly.const A)    a        = A .fam .fm a
    WFam-fm μPoly.var          (inF i)  = WFam-fm Q i
    WFam-fm (P μPoly.+ Q)      (inj₁ x) = WFam-fm P x
    WFam-fm (P μPoly.+ Q)      (inj₂ y) = WFam-fm Q y
    WFam-fm (P μPoly.× Q)      (x , y)  = prod (WFam-fm P x) (WFam-fm Q y)
    WFam-fm (μPoly.Mon P)      i        = fobj (WFam-fm P i)

    WFam-subst : (P : μPoly cat) → ∀ {x y} → WIdx-≈ poly (idx-of-μ P) x y → WFam-fm P x ⇒ WFam-fm P y
    WFam-subst μPoly.one _ = id _
    WFam-subst (μPoly.const A) {x} {y} eq = A .fam .subst eq
    WFam-subst μPoly.var {inF i₁} {inF i₂} eq = WFam-subst Q eq
    WFam-subst (P μPoly.+ Q) {inj₁ _} {inj₁ _} eq = WFam-subst P eq
    WFam-subst (P μPoly.+ Q) {inj₂ _} {inj₂ _} eq = WFam-subst Q eq
    WFam-subst (P μPoly.+ Q) {inj₁ _} {inj₂ _} ()
    WFam-subst (P μPoly.+ Q) {inj₂ _} {inj₁ _} ()
    WFam-subst (P μPoly.× Q) {_ , _} {_ , _} (e₁ , e₂) =
      prod-m (WFam-subst P e₁) (WFam-subst Q e₂)
    WFam-subst (μPoly.Mon P) eq = fmor (WFam-subst P eq)

    WFam-refl* : (P : μPoly cat) → ∀ {x} →
                    WFam-subst P (WIdx-≈-refl poly (idx-of-μ P) {x}) ≈ id _
    WFam-refl* μPoly.one         = isEquiv .refl
    WFam-refl* (μPoly.const A) {x} = A .fam .refl*
    WFam-refl* μPoly.var {inF i} = WFam-refl* Q {i}
    WFam-refl* (P μPoly.+ Q) {inj₁ x} = WFam-refl* P {x}
    WFam-refl* (P μPoly.+ Q) {inj₂ y} = WFam-refl* Q {y}
    WFam-refl* (P μPoly.× Q) {x , y}  =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-refl* P {x}) (WFam-refl* Q {y}) ⟩
        prod-m (id _) (id _)
      ≈⟨ prod-m-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    WFam-refl* (μPoly.Mon P) {x} =
      begin
        fmor (WFam-subst P _)
      ≈⟨ fmor-cong (WFam-refl* P {x}) ⟩
        fmor (id _)
      ≈⟨ fmor-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv

    WFam-trans* : (P : μPoly cat) → ∀ {x y z}
                     (e₁ : WIdx-≈ poly (idx-of-μ P) y z) (e₂ : WIdx-≈ poly (idx-of-μ P) x y) →
                     WFam-subst P (WIdx-≈-trans poly (idx-of-μ P) e₂ e₁) ≈
                     (WFam-subst P e₁ ∘ WFam-subst P e₂)
    WFam-trans* μPoly.one _ _ = isEquiv .sym id-left
    WFam-trans* (μPoly.const A) e₁ e₂ = A .fam .trans* e₁ e₂
    WFam-trans* μPoly.var {inF _} {inF _} {inF _} e₁ e₂ =
      WFam-trans* Q e₁ e₂
    WFam-trans* (P μPoly.+ Q) {inj₁ _} {inj₁ _} {inj₁ _} e₁ e₂ = WFam-trans* P e₁ e₂
    WFam-trans* (P μPoly.+ Q) {inj₂ _} {inj₂ _} {inj₂ _} e₁ e₂ = WFam-trans* Q e₁ e₂
    WFam-trans* (P μPoly.× Q) {_ , _} {_ , _} {_ , _} (e₁ , f₁) (e₂ , f₂) =
      begin
        prod-m (WFam-subst P _) (WFam-subst Q _)
      ≈⟨ prod-m-cong (WFam-trans* P e₁ e₂) (WFam-trans* Q f₁ f₂) ⟩
        prod-m (WFam-subst P e₁ ∘ WFam-subst P e₂) (WFam-subst Q f₁ ∘ WFam-subst Q f₂)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P e₁) (WFam-subst Q f₁) ∘ prod-m (WFam-subst P e₂) (WFam-subst Q f₂)
      ∎ where open ≈-Reasoning isEquiv
    WFam-trans* (μPoly.Mon P) e₁ e₂ =
      begin
        fmor (WFam-subst P _)
      ≈⟨ fmor-cong (WFam-trans* P e₁ e₂) ⟩
        fmor (WFam-subst P e₁ ∘ WFam-subst P e₂)
      ≈⟨ fmor-comp _ _ ⟩
        fmor (WFam-subst P e₁) ∘ fmor (WFam-subst P e₂)
      ∎ where open ≈-Reasoning isEquiv

    WFam : Fam (WSetoid poly) 𝒟
    WFam .fm (inF i)                            = WFam-fm Q i
    WFam .subst {inF _} {inF _} eq              = WFam-subst Q eq
    WFam .refl* {inF _}                         = WFam-refl* Q
    WFam .trans* {inF _} {inF _} {inF _} e₁ e₂  = WFam-trans* Q e₁ e₂

    WObj : Obj
    WObj .idx = WSetoid poly
    WObj .fam = WFam

    embed-idx : (P : μPoly cat) → μPoly-obj P WObj .idx .Carrier → WIdx poly (idx-of-μ P)
    embed-idx μPoly.one         (lift tt)  = lift tt
    embed-idx (μPoly.const A)   a          = a
    embed-idx μPoly.var         w          = w
    embed-idx (P μPoly.+ Q)     (inj₁ x)   = inj₁ (embed-idx P x)
    embed-idx (P μPoly.+ Q)     (inj₂ y)   = inj₂ (embed-idx Q y)
    embed-idx (P μPoly.× Q)     (x , y)    = (embed-idx P x , embed-idx Q y)
    embed-idx (μPoly.Mon P)     i          = embed-idx P i   -- Mon preserves idx

    embed-≈ : (P : μPoly cat) → ∀ {x y} →
              μPoly-obj P WObj .idx ._≈s_ x y → WIdx-≈ poly (idx-of-μ P) (embed-idx P x) (embed-idx P y)
    embed-≈ μPoly.one _                             = tt
    embed-≈ (μPoly.const A) eq                      = eq
    embed-≈ μPoly.var eq                            = eq
    embed-≈ (P μPoly.+ Q) {inj₁ _} {inj₁ _} eq      = embed-≈ P eq
    embed-≈ (P μPoly.+ Q) {inj₂ _} {inj₂ _} eq      = embed-≈ Q eq
    embed-≈ (P μPoly.× Q) {_ , _} {_ , _} (e₁ , e₂) = (embed-≈ P e₁ , embed-≈ Q e₂)
    embed-≈ (μPoly.Mon P)  eq                       = embed-≈ P eq

    embed-fam : (P : μPoly cat) (i : μPoly-obj P WObj .idx .Carrier) →
                μPoly-obj P WObj .fam .fm i ⇒ WFam-fm P (embed-idx P i)
    embed-fam μPoly.one         (lift tt)  = id _
    embed-fam (μPoly.const A)   a          = id _
    embed-fam μPoly.var         (inF _)    = id _
    embed-fam (P μPoly.+ Q)     (inj₁ x)   = embed-fam P x
    embed-fam (P μPoly.+ Q)     (inj₂ y)   = embed-fam Q y
    embed-fam (P μPoly.× Q)     (x , y)    = prod-m (embed-fam P x) (embed-fam Q y)
    embed-fam (μPoly.Mon P)     i          = fmor (embed-fam P i)

    embed-fam-natural : (P : μPoly cat) → ∀ {x₁ x₂} (e : μPoly-obj P WObj .idx ._≈s_ x₁ x₂) →
                        (embed-fam P x₂ ∘ μPoly-obj P WObj .fam .subst e) ≈
                        (WFam-subst P (embed-≈ P e) ∘ embed-fam P x₁)
    embed-fam-natural μPoly.one _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (μPoly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural μPoly.var {inF _} {inF _} _ = isEquiv .trans id-left (≈-sym id-right)
    embed-fam-natural (P μPoly.+ Q) {inj₁ _} {inj₁ _} e = embed-fam-natural P e
    embed-fam-natural (P μPoly.+ Q) {inj₂ _} {inj₂ _} e = embed-fam-natural Q e
    embed-fam-natural (P μPoly.× Q) {x₁ , y₁} {x₂ , y₂} (e , f) =
      begin
        prod-m (embed-fam P x₂) (embed-fam Q y₂) ∘ prod-m _ _
      ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
        prod-m (embed-fam P x₂ ∘ _) (embed-fam Q y₂ ∘ _)
      ≈⟨ prod-m-cong (embed-fam-natural P e) (embed-fam-natural Q f) ⟩
        prod-m (WFam-subst P (embed-≈ P e) ∘ embed-fam P x₁) (WFam-subst Q (embed-≈ Q f) ∘ embed-fam Q y₁)
      ≈⟨ pair-functorial _ _ _ _ ⟩
        prod-m (WFam-subst P (embed-≈ P e)) (WFam-subst Q (embed-≈ Q f)) ∘ prod-m (embed-fam P x₁) (embed-fam Q y₁)
      ∎ where open ≈-Reasoning isEquiv
    embed-fam-natural (μPoly.Mon P) {x₁} {x₂} e =
      begin
        fmor (embed-fam P x₂) ∘ fmor _
      ≈⟨ ≈-sym (fmor-comp _ _) ⟩
        fmor (embed-fam P x₂ ∘ _)
      ≈⟨ fmor-cong (embed-fam-natural P e) ⟩
        fmor (WFam-subst P (embed-≈ P e) ∘ embed-fam P x₁)
      ≈⟨ fmor-comp _ _ ⟩
        fmor (WFam-subst P (embed-≈ P e)) ∘ fmor (embed-fam P x₁)
      ∎ where open ≈-Reasoning isEquiv

    inF-mor : Mor (μPoly-obj Q WObj) WObj
    inF-mor .idxf .PS._⇒_.func i          = inF (embed-idx Q i)
    inF-mor .idxf .PS._⇒_.func-resp-≈ eq  = embed-≈ Q eq
    inF-mor .famf .transf i               = embed-fam Q i
    inF-mor .famf .natural e              = embed-fam-natural Q e

    module _ {y : Obj} (alg : Mor (μPoly-obj Q y) y) where

      project-idx : (P : μPoly cat) → WIdx poly (idx-of-μ P) → μPoly-obj P y .idx .Carrier
      project-idx μPoly.one       _         = lift tt
      project-idx (μPoly.const A) a         = a
      project-idx μPoly.var       (inF i)   = alg .idxf .PS._⇒_.func (project-idx Q i)
      project-idx (P μPoly.+ Q)   (inj₁ x)  = inj₁ (project-idx P x)
      project-idx (P μPoly.+ Q)   (inj₂ z)  = inj₂ (project-idx Q z)
      project-idx (P μPoly.× Q)   (x , z)   = (project-idx P x , project-idx Q z)
      project-idx (μPoly.Mon P)   i         = project-idx P i

      project-≈ : (P : μPoly cat) → ∀ {x z} → WIdx-≈ poly (idx-of-μ P) x z →
                  μPoly-obj P y .idx ._≈s_ (project-idx P x) (project-idx P z)
      project-≈ μPoly.one _ = tt
      project-≈ (μPoly.const A) eq = eq
      project-≈ μPoly.var {inF _} {inF _} eq =
        alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)
      project-≈ (P μPoly.+ Q) {inj₁ _} {inj₁ _} eq = project-≈ P eq
      project-≈ (P μPoly.+ Q) {inj₂ _} {inj₂ _} eq = project-≈ Q eq
      project-≈ (P μPoly.× Q) {_ , _} {_ , _} (e , f) = (project-≈ P e , project-≈ Q f)
      project-≈ (μPoly.Mon P)   eq = project-≈ P eq

      project-fam : (P : μPoly cat) (i : WIdx poly (idx-of-μ P)) →
                    WFam-fm P i ⇒ μPoly-obj P y .fam .fm (project-idx P i)
      project-fam μPoly.one _            = id _
      project-fam (μPoly.const A) a      = id _
      project-fam μPoly.var (inF i)      = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      project-fam (P μPoly.+ Q) (inj₁ x) = project-fam P x
      project-fam (P μPoly.+ Q) (inj₂ z) = project-fam Q z
      project-fam (P μPoly.× Q) (x , z)  = prod-m (project-fam P x) (project-fam Q z)
      project-fam (μPoly.Mon P) i        = fmor (project-fam P i)

      project-fam-natural : (P : μPoly cat) → ∀ {x z} (e : WIdx-≈ poly (idx-of-μ P) x z) →
                            (project-fam P z ∘ WFam-subst P e) ≈
                            (μPoly-obj P y .fam .subst (project-≈ P e) ∘ project-fam P x)
      project-fam-natural μPoly.one _ = isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural (μPoly.const A) _ = isEquiv .trans id-left (≈-sym id-right)
      project-fam-natural μPoly.var {inF i₁} {inF i₂} eq =
        begin
          (alg .famf .transf (project-idx Q i₂) ∘ project-fam Q i₂) ∘ WFam-subst Q eq
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (project-idx Q i₂) ∘ (project-fam Q i₂ ∘ WFam-subst Q eq)
        ≈⟨ ∘-cong (isEquiv .refl) (project-fam-natural Q eq) ⟩
          alg .famf .transf (project-idx Q i₂) ∘
            (μPoly-obj Q y .fam .subst (project-≈ Q eq) ∘ project-fam Q i₁)
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (project-idx Q i₂) ∘
            μPoly-obj Q y .fam .subst (project-≈ Q eq)) ∘ project-fam Q i₁
        ≈⟨ ∘-cong (alg .famf .natural (project-≈ Q eq)) (isEquiv .refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)) ∘ alg .famf .transf (project-idx Q i₁)) ∘ project-fam Q i₁
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)) ∘
            (alg .famf .transf (project-idx Q i₁) ∘ project-fam Q i₁)
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural (P μPoly.+ Q) {inj₁ _} {inj₁ _} e = project-fam-natural P e
      project-fam-natural (P μPoly.+ Q) {inj₂ _} {inj₂ _} e = project-fam-natural Q e
      project-fam-natural (P μPoly.× Q) {x₁ , z₁} {x₂ , z₂} (e , f) =
        begin
          prod-m (project-fam P x₂) (project-fam Q z₂) ∘ prod-m _ _
        ≈⟨ ≈-sym (pair-functorial _ _ _ _) ⟩
          prod-m (project-fam P x₂ ∘ _) (project-fam Q z₂ ∘ _)
        ≈⟨ prod-m-cong (project-fam-natural P e) (project-fam-natural Q f) ⟩
          prod-m (_ ∘ project-fam P x₁) (_ ∘ project-fam Q z₁)
        ≈⟨ pair-functorial _ _ _ _ ⟩
          prod-m _ _ ∘ prod-m (project-fam P x₁) (project-fam Q z₁)
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural (μPoly.Mon P) {x₁} {x₂} e =
        begin
          fmor (project-fam P x₂) ∘ fmor _
        ≈⟨ ≈-sym (fmor-comp _ _) ⟩
          fmor (project-fam P x₂ ∘ _)
        ≈⟨ fmor-cong (project-fam-natural P e) ⟩
          fmor (_ ∘ project-fam P x₁)
        ≈⟨ fmor-comp _ _ ⟩
          fmor _ ∘ fmor (project-fam P x₁)
        ∎ where open ≈-Reasoning isEquiv

      fold : Mor WObj y
      fold .idxf .PS._⇒_.func (inF i)                   = alg .idxf .PS._⇒_.func (project-idx Q i)
      fold .idxf .PS._⇒_.func-resp-≈ {inF _} {inF _} eq = alg .idxf .PS._⇒_.func-resp-≈ (project-≈ Q eq)
      fold .famf .transf (inF i)                        = alg .famf .transf (project-idx Q i) ∘ project-fam Q i
      fold .famf .natural {inF _} {inF _} eq            = project-fam-natural μPoly.var eq

    -- Open (parametric) fold: takes algebra in extended context Γ ⊗ μPoly-obj Q y ⇒ y
    -- and produces Γ ⊗ μ Q ⇒ y. Threads γ through the structural recursion;
    -- right-strength of L handles the Mon case.
    module Open {Γ y : Obj} (alg : Mor (Γ ⊗ μPoly-obj Q y) y) where
      open Obj
      open Mor

      -- idx-level: descend the W-tree, applying alg at var positions with γ fixed.
      project-idx-open : (P : μPoly cat) → Γ .idx .Carrier → WIdx poly (idx-of-μ P) →
                         μPoly-obj P y .idx .Carrier
      project-idx-open μPoly.one       _ _         = lift tt
      project-idx-open (μPoly.const A) _ a         = a
      project-idx-open μPoly.var       γ (inF i)   =
        alg .idxf .PS._⇒_.func (γ , project-idx-open Q γ i)
      project-idx-open (P μPoly.+ R)   γ (inj₁ x)  = inj₁ (project-idx-open P γ x)
      project-idx-open (P μPoly.+ R)   γ (inj₂ z)  = inj₂ (project-idx-open R γ z)
      project-idx-open (P μPoly.× R)   γ (x , z)   = (project-idx-open P γ x , project-idx-open R γ z)
      project-idx-open (μPoly.Mon P)   γ i         = project-idx-open P γ i

      project-≈-open : (P : μPoly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
                       (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂) (i₁≈i₂ : WIdx-≈ poly (idx-of-μ P) x z) →
                       μPoly-obj P y .idx ._≈s_
                         (project-idx-open P γ₁ x) (project-idx-open P γ₂ z)
      project-≈-open μPoly.one _ _ = tt
      project-≈-open (μPoly.const A) _ eq = eq
      project-≈-open μPoly.var {γ₁} {γ₂} {inF _} {inF _} γ₁≈γ₂ eq =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ eq)
      project-≈-open (P μPoly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ eq = project-≈-open P γ₁≈γ₂ eq
      project-≈-open (P μPoly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ eq = project-≈-open R γ₁≈γ₂ eq
      project-≈-open (P μPoly.× R) {x = _ , _} {_ , _} γ₁≈γ₂ (e , f) =
        project-≈-open P γ₁≈γ₂ e , project-≈-open R γ₁≈γ₂ f
      project-≈-open (μPoly.Mon P) γ₁≈γ₂ eq = project-≈-open P γ₁≈γ₂ eq

      -- fam-level: input is Γ-fibre ⊗ W-fibre; output is the corresponding μPoly-obj y-fibre.
      project-fam-open : (P : μPoly cat) (γ : Γ .idx .Carrier)
                         (i : WIdx poly (idx-of-μ P)) →
                         prod (Γ .fam .fm γ) (WFam-fm P i) ⇒
                         μPoly-obj P y .fam .fm (project-idx-open P γ i)
      project-fam-open μPoly.one         _ _         = HasTerminal.to-terminal T
      project-fam-open (μPoly.const A)   _ _         = p₂
      project-fam-open μPoly.var         γ (inF i)   =
        alg .famf .transf (γ , project-idx-open Q γ i) ∘ pair p₁ (project-fam-open Q γ i)
      project-fam-open (P μPoly.+ R)     γ (inj₁ x)  = project-fam-open P γ x
      project-fam-open (P μPoly.+ R)     γ (inj₂ z)  = project-fam-open R γ z
      project-fam-open (P μPoly.× R)     γ (x , z)   =
        pair (project-fam-open P γ x ∘ pair p₁ (p₁ ∘ p₂))
             (project-fam-open R γ z ∘ pair p₁ (p₂ ∘ p₂))
      project-fam-open (μPoly.Mon P)     γ i         =
        fmor (project-fam-open P γ i) ∘ right-strength

      -- Naturality of project-fam-open w.r.t. γ and W-tree equivalences.
      project-fam-natural-open :
        (P : μPoly cat) → ∀ {γ₁ γ₂ : Γ .idx .Carrier} {x z}
        (γ₁≈γ₂ : Γ .idx ._≈s_ γ₁ γ₂)
        (i₁≈i₂ : WIdx-≈ poly (idx-of-μ P) x z) →
        (project-fam-open P γ₂ z ∘
          prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂)) ≈
        (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂) ∘ project-fam-open P γ₁ x)
      project-fam-natural-open μPoly.one _ _ =
        HasTerminal.to-terminal-unique T _ _
      project-fam-natural-open (μPoly.const A) {x = a} {z = b} _ i₁≈i₂ =
        begin
          p₂ ∘ prod-m _ (A .fam .subst i₁≈i₂)
        ≈⟨ pair-p₂ _ _ ⟩
          A .fam .subst i₁≈i₂ ∘ p₂
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open μPoly.var {γ₁} {γ₂} {inF i₁} {inF i₂} γ₁≈γ₂ i₁≈i₂ =
        begin
          (alg .famf .transf (γ₂ , _) ∘ pair p₁ (project-fam-open Q γ₂ i₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂)
        ≈⟨ assoc _ _ _ ⟩
          alg .famf .transf (γ₂ , _) ∘
            (pair p₁ (project-fam-open Q γ₂ i₂) ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst Q i₁≈i₂))
        ≈⟨ ∘-cong (isEquiv .refl) (pair-natural _ _ _) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (p₁ ∘ prod-m _ _) (project-fam-open Q γ₂ i₂ ∘ prod-m _ _)
        ≈⟨ ∘-cong (isEquiv .refl)
             (pair-cong (pair-p₁ _ _) (project-fam-natural-open Q γ₁≈γ₂ i₁≈i₂)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁)
                 (μPoly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂) ∘ project-fam-open Q γ₁ i₁)
        ≈⟨ ≈-sym (∘-cong (isEquiv .refl) (pair-compose _ _ _ _)) ⟩
          alg .famf .transf (γ₂ , _) ∘
            (prod-m (Γ .fam .subst γ₁≈γ₂) (μPoly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂))
              ∘ pair p₁ (project-fam-open Q γ₁ i₁))
        ≈⟨ ≈-sym (assoc _ _ _) ⟩
          (alg .famf .transf (γ₂ , _) ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (μPoly-obj Q y .fam .subst (project-≈-open Q γ₁≈γ₂ i₁≈i₂)))
            ∘ pair p₁ (project-fam-open Q γ₁ i₁)
        ≈⟨ ∘-cong (alg .famf .natural (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)) (isEquiv .refl) ⟩
          (y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂))
            ∘ alg .famf .transf (γ₁ , _))
            ∘ pair p₁ (project-fam-open Q γ₁ i₁)
        ≈⟨ assoc _ _ _ ⟩
          y .fam .subst (alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂))
            ∘ (alg .famf .transf (γ₁ , _) ∘ pair p₁ (project-fam-open Q γ₁ i₁))
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open (P μPoly.+ R) {x = inj₁ _} {inj₁ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural-open P γ₁≈γ₂ i₁≈i₂
      project-fam-natural-open (P μPoly.+ R) {x = inj₂ _} {inj₂ _} γ₁≈γ₂ i₁≈i₂ =
        project-fam-natural-open R γ₁≈γ₂ i₁≈i₂
      project-fam-natural-open (P μPoly.× R) {γ₁} {γ₂} {x₁ , z₁} {x₂ , z₂} γ₁≈γ₂ (eP , eR) =
        begin
          pair (project-fam-open P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂))
               (project-fam-open R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂))
            ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (prod-m (WFam-subst P eP) (WFam-subst R eR))
        ≈⟨ pair-natural _ _ _ ⟩
          pair ((project-fam-open P γ₂ x₂ ∘ pair p₁ (p₁ ∘ p₂)) ∘ prod-m _ _)
               ((project-fam-open R γ₂ z₂ ∘ pair p₁ (p₂ ∘ p₂)) ∘ prod-m _ _)
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (project-fam-open P γ₂ x₂ ∘ (pair p₁ (p₁ ∘ p₂) ∘ prod-m _ _))
               (project-fam-open R γ₂ z₂ ∘ (pair p₁ (p₂ ∘ p₂) ∘ prod-m _ _))
        ≈⟨ pair-cong
             (∘-cong (isEquiv .refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (isEquiv .refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₁ _ _) (isEquiv .refl)) (assoc _ _ _))))))))
             (∘-cong (isEquiv .refl)
               (≈-trans (pair-natural _ _ _)
                 (pair-cong (pair-p₁ _ _)
                   (≈-trans (assoc _ _ _)
                     (≈-trans (∘-cong (isEquiv .refl) (pair-p₂ _ _))
                       (≈-trans (≈-sym (assoc _ _ _))
                         (≈-trans (∘-cong (pair-p₂ _ _) (isEquiv .refl)) (assoc _ _ _)))))))) ⟩
          pair (project-fam-open P γ₂ x₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst P eP ∘ (p₁ ∘ p₂)))
               (project-fam-open R γ₂ z₂ ∘ pair (Γ .fam .subst γ₁≈γ₂ ∘ p₁) (WFam-subst R eR ∘ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (∘-cong (isEquiv .refl) (≈-sym (pair-compose _ _ _ _)))
                     (∘-cong (isEquiv .refl) (≈-sym (pair-compose _ _ _ _))) ⟩
          pair (project-fam-open P γ₂ x₂ ∘
                 (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P eP) ∘ pair p₁ (p₁ ∘ p₂)))
               (project-fam-open R γ₂ z₂ ∘
                 (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst R eR) ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ pair-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
          pair ((project-fam-open P γ₂ x₂ ∘ prod-m _ _) ∘ pair p₁ (p₁ ∘ p₂))
               ((project-fam-open R γ₂ z₂ ∘ prod-m _ _) ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (∘-cong (project-fam-natural-open P γ₁≈γ₂ eP) (isEquiv .refl))
                     (∘-cong (project-fam-natural-open R γ₁≈γ₂ eR) (isEquiv .refl)) ⟩
          pair ((μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ eP) ∘ project-fam-open P γ₁ x₁)
                  ∘ pair p₁ (p₁ ∘ p₂))
               ((μPoly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ eR) ∘ project-fam-open R γ₁ z₁)
                  ∘ pair p₁ (p₂ ∘ p₂))
        ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
          pair (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ eP)
                 ∘ (project-fam-open P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂)))
               (μPoly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ eR)
                 ∘ (project-fam-open R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂)))
        ≈⟨ ≈-sym (pair-compose _ _ _ _) ⟩
          prod-m (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ eP))
                 (μPoly-obj R y .fam .subst (project-≈-open R γ₁≈γ₂ eR))
            ∘ pair (project-fam-open P γ₁ x₁ ∘ pair p₁ (p₁ ∘ p₂))
                   (project-fam-open R γ₁ z₁ ∘ pair p₁ (p₂ ∘ p₂))
        ∎ where open ≈-Reasoning isEquiv
      project-fam-natural-open (μPoly.Mon P) {γ₁} {γ₂} {x} {z} γ₁≈γ₂ i₁≈i₂ =
        begin
          (fmor (project-fam-open P γ₂ z) ∘ right-strength) ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (fmor (WFam-subst P i₁≈i₂))
        ≈⟨ assoc _ _ _ ⟩
          fmor (project-fam-open P γ₂ z) ∘
            (right-strength ∘ prod-m (Γ .fam .subst γ₁≈γ₂) (fmor (WFam-subst P i₁≈i₂)))
        ≈⟨ ∘-cong (isEquiv .refl)
             (isEquiv .sym (right-strength-natural _ _)) ⟩
          fmor (project-fam-open P γ₂ z) ∘
            (fmor (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂)) ∘ right-strength)
        ≈⟨ isEquiv .sym (assoc _ _ _) ⟩
          (fmor (project-fam-open P γ₂ z) ∘
            fmor (prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂))) ∘ right-strength
        ≈⟨ ∘-cong (isEquiv .sym (fmor-comp _ _)) (isEquiv .refl) ⟩
          fmor (project-fam-open P γ₂ z ∘
            prod-m (Γ .fam .subst γ₁≈γ₂) (WFam-subst P i₁≈i₂)) ∘ right-strength
        ≈⟨ ∘-cong (fmor-cong (project-fam-natural-open P γ₁≈γ₂ i₁≈i₂)) (isEquiv .refl) ⟩
          fmor (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂) ∘
                project-fam-open P γ₁ x) ∘ right-strength
        ≈⟨ ∘-cong (fmor-comp _ _) (isEquiv .refl) ⟩
          (fmor (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂)) ∘
            fmor (project-fam-open P γ₁ x)) ∘ right-strength
        ≈⟨ assoc _ _ _ ⟩
          fmor (μPoly-obj P y .fam .subst (project-≈-open P γ₁≈γ₂ i₁≈i₂)) ∘
            (fmor (project-fam-open P γ₁ x) ∘ right-strength)
        ∎ where open ≈-Reasoning isEquiv

      fold-open : Mor (Γ ⊗ WObj) y
      fold-open .idxf .PS._⇒_.func (γ , inF i) =
        alg .idxf .PS._⇒_.func (γ , project-idx-open Q γ i)
      fold-open .idxf .PS._⇒_.func-resp-≈ {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        alg .idxf .PS._⇒_.func-resp-≈ (γ₁≈γ₂ , project-≈-open Q γ₁≈γ₂ i₁≈i₂)
      fold-open .famf .transf (γ , inF i) =
        alg .famf .transf (γ , project-idx-open Q γ i) ∘
          pair p₁ (project-fam-open Q γ i)
      fold-open .famf .natural {γ₁ , inF _} {γ₂ , inF _} (γ₁≈γ₂ , i₁≈i₂) =
        project-fam-natural-open μPoly.var γ₁≈γ₂ i₁≈i₂

  hasMu-μPoly : HasMu-μPoly
  hasMu-μPoly .HasMu-μPoly.μ Q          = W-types-μ.WObj Q
  hasMu-μPoly .HasMu-μPoly.inμ Q        = W-types-μ.inF-mor Q
  hasMu-μPoly .HasMu-μPoly.⦅_⦆ {Γ} {Q}  = W-types-μ.Open.fold-open Q
