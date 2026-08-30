{-# OPTIONS --prop --postfix-projections --safe #-}

-- The fundamental lemma: a term's value is related to its index at a
-- related environment, and the relation applied to the inputs is related to the term's fibre map plus
-- the control dependence at the control input's value. Soundness of values at every type and of dependence at
-- first-order types.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Unary.All as Every using () renaming (All to Every)
open import Data.List using ([]; _∷_)
open import Data.Unit using (tt)
import prop
open import prop using (_∧_; ∃; Prf; ⟪_⟫; _,_; proj₁; proj₂)
open import prop-setoid using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym) renaming (subst to ≡-subst)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation; sort-vals-setoid)
open import categories using (Category; HasExponentials; HasStrongCoproducts)
import indexed-family
import commutative-monoid

module ho-agreement
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (ctrl-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  (let module S = CommutativeSemiring S)
  (+-idem : ∀ x → (x S.+ x) S.≈ x)
  (let module S⊑ = commutative-monoid.AdditivePreorder S.additive (λ {x} → +-idem x))
  (c-idem : (ctrl-weight S.· ctrl-weight) S.≈ ctrl-weight)
  (c-bound : ∀ x → (ctrl-weight S.· x) S⊑.⊑ ctrl-weight)
  where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig renaming (_,_ to _▸_) hiding (cons)
open import language-operational.type-substitution Sig using (unfold₁; unfold₁-inst)
open import language-operational.evaluation Sig S ℐ ctrl-weight

open import ho-relation S ctrl-weight Sig ℐ +-idem c-idem c-bound

args-idx : ∀ {Γ is} (Ms : Every (λ σ → Γ ⊢ base σ) is) (gi : IxC Γ) → sort-vals is
args-idx {is = is} Ms gi =
  collect is .Fam⟨𝒞⟩μ.idxf .sfunc (𝒟-arg-product is .idxf .sfunc (⟦ Ms ⟧tms .idxf .sfunc gi))

private
  bool-idx : ∀ (b : Ix (unit [+] unit)) →
             Ix._≈_ (unit [+] unit)
               (interp.Fam⟨F⟩-preserves-bool .idxf .sfunc b) b
  bool-idx (inj₁ _) = prop.tt
  bool-idx (inj₂ _) = prop.tt

  ValRel-bool : ∀ (b i : Ix (unit [+] unit)) → Prf (Ix._≈_ (unit [+] unit) i b) →
                ValRel (unit [+] unit) (bool→val b) i
  ValRel-bool (inj₁ _) i e = lift tt , tt , e
  ValRel-bool (inj₂ _) i e = lift tt , tt , e

private
  case-idx : ∀ {Γ τ₁ τ₂ τ} (sc : Γ ⊢ τ₁ [+] τ₂) (t₁ : Γ ▸ τ₁ ⊢ τ) (t₂ : Γ ▸ τ₂ ⊢ τ) gi
             (k : Ix (τ₁ [+] τ₂)) → Ix._≈_ (τ₁ [+] τ₂) (⟦ sc ⟧tm .idxf .sfunc gi) k →
             Ix._≈_ τ (⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi)
               (copair (elimF (ctrl-dep τ) ⟦ t₁ ⟧tm) (elimF (ctrl-dep τ) ⟦ t₂ ⟧tm) .idxf .sfunc (gi , k))
  case-idx {Γ} {τ₁} {τ₂} {τ} sc t₁ t₂ gi k e =
    copair (elimF (ctrl-dep τ) ⟦ t₁ ⟧tm) (elimF (ctrl-dep τ) ⟦ t₂ ⟧tm) .idxf .sfunc-resp-≈
      {gi , ⟦ sc ⟧tm .idxf .sfunc gi} {gi , k} (IxC.refl Γ {gi} , e)

  brel-idx : ∀ {Γ is} (ω : rel is) (Ms : Every (λ σ → Γ ⊢ base σ) is) gi (vs : sort-vals is) →
             Setoid._≈_ (sort-vals-setoid sort-index is) (args-idx Ms gi) vs →
             Ix._≈_ (unit [+] unit) (⟦ brel ω Ms ⟧tm .idxf .sfunc gi) (rel-pred ω .sfunc vs)
  brel-idx ω Ms gi vs args-eq =
    Ix.trans (unit [+] unit)
      {⟦ brel ω Ms ⟧tm .idxf .sfunc gi} {rel-pred ω .sfunc (args-idx Ms gi)} {rel-pred ω .sfunc vs}
      (bool-idx (rel-pred ω .sfunc (args-idx Ms gi))) (rel-pred ω .sfunc-resp-≈ args-eq)

private
  rec-idx : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) gi (i : Ix (μ τ₀)) →
            Ix._≈_ σr
              (⟦ s ⟧tm .idxf .sfunc (gi , fold-map τ₀ σr τ₀ ⟦ s ⟧tm .idxf .sfunc (gi , unroll-mor τ₀ .idxf .sfunc i)))
              (fold-map τ₀ σr (var zero) ⟦ s ⟧tm .idxf .sfunc (gi , i))
  rec-idx {Γ} {τ₀} {σr} s gi i =
    Ix.trans σr (Ix.sym σr (idx-eq (fold-map-rec τ₀ σr ⟦ s ⟧tm) (gi , i₀)))
      (Fv .idxf .sfunc-resp-≈ {gi , roll-mor τ₀ .idxf .sfunc i₀} {gi , i} (IxC.refl Γ {gi} , idx-eq (roll-unroll τ₀) i))
    where
    i₀ = unroll-mor τ₀ .idxf .sfunc i
    Fv = fold-map τ₀ σr (var zero) ⟦ s ⟧tm

  inl-idx : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ₁ σ₂ : type 1) gi {i} {i' : Ix (σ₁ [ μ τ₀ ])} →
            Ix._≈_ ((σ₁ [+] σ₂) [ μ τ₀ ]) i (inj₁ i') →
            Ix._≈_ ((σ₁ [+] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i))
                                        (inj₁ (fold-map τ₀ σr σ₁ ⟦ s ⟧tm .idxf .sfunc (gi , i')))
  inl-idx {Γ} {τ₀} {σr} s σ₁ σ₂ gi {i} {i'} e₀ =
    Ix.trans ((σ₁ [+] σ₂) [ σr ]) {F₊ .idxf .sfunc (gi , i)} {F₊ .idxf .sfunc (gi , inj₁ i')} {inj₁ (F₁ .idxf .sfunc (gi , i'))}
      (F₊ .idxf .sfunc-resp-≈ {gi , i} {gi , inj₁ i'} (IxC.refl Γ {gi} , e₀))
      (idx-eq (fold-map-inl τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i'))
    where
    F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
    F₁ = fold-map τ₀ σr σ₁ ⟦ s ⟧tm

  inr-idx : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ₁ σ₂ : type 1) gi {i} {i' : Ix (σ₂ [ μ τ₀ ])} →
            Ix._≈_ ((σ₁ [+] σ₂) [ μ τ₀ ]) i (inj₂ i') →
            Ix._≈_ ((σ₁ [+] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i))
                                        (inj₂ (fold-map τ₀ σr σ₂ ⟦ s ⟧tm .idxf .sfunc (gi , i')))
  inr-idx {Γ} {τ₀} {σr} s σ₁ σ₂ gi {i} {i'} e₀ =
    Ix.trans ((σ₁ [+] σ₂) [ σr ]) {F₊ .idxf .sfunc (gi , i)} {F₊ .idxf .sfunc (gi , inj₂ i')} {inj₂ (F₂ .idxf .sfunc (gi , i'))}
      (F₊ .idxf .sfunc-resp-≈ {gi , i} {gi , inj₂ i'} (IxC.refl Γ {gi} , e₀))
      (idx-eq (fold-map-inr τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i'))
    where
    F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
    F₂ = fold-map τ₀ σr σ₂ ⟦ s ⟧tm

  pair-idx : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ₁ σ₂ : type 1) gi
             (i : Ix ((σ₁ [×] σ₂) [ μ τ₀ ])) →
             Ix._≈_ ((σ₁ [×] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i))
               (fold-map τ₀ σr σ₁ ⟦ s ⟧tm .idxf .sfunc (gi , proj₁ i) , fold-map τ₀ σr σ₂ ⟦ s ⟧tm .idxf .sfunc (gi , proj₂ i))
  pair-idx {Γ} {τ₀} {σr} s σ₁ σ₂ gi i = idx-eq (fold-map-pair τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i)

  module MuShape {Γ} (τ₀ : type 1) (σr : type 0) (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (τ' : type 2) where
    τμ = τ' [ μ τ₀ ]₁
    τₛ = τ' [ σr ]₁
    T = τₛ [ μ τₛ ]
    eμ = unfold₁-inst τ' (μ τ₀)
    eₛ = unfold₁-inst τ' σr
    Cμ = ty-cast eμ
    Cₛ = ty-cast eₛ
    Fu = fold-map τ₀ σr (unfold₁ τ') ⟦ s ⟧tm
    Fμ = fold-map τ₀ σr (μ τ') ⟦ s ⟧tm

    module Idx (gi : IxC Γ) (i : Ix ((μ τ') [ μ τ₀ ])) where
      iu = unroll-mor τμ .idxf .sfunc i
      i₀ = ty-cast (sym eμ) .idxf .sfunc iu
      Iu = Fu .idxf .sfunc (gi , i₀)
      Iμ = Fμ .idxf .sfunc (gi , i)
      a = Cₛ .idxf .sfunc Iu
      b = roll-mor τμ .idxf .sfunc (Cμ .idxf .sfunc i₀)
      Ib = Fμ .idxf .sfunc (gi , b)
      Ec : Ix._≈_ (τμ [ μ τμ ]) (Cμ .idxf .sfunc i₀) iu
      Ec = ty-cast-cancel eμ iu
      Er : Ix._≈_ (μ τμ) b (roll-mor τμ .idxf .sfunc iu)
      Er = roll-mor τμ .idxf .sfunc-resp-≈ {Cμ .idxf .sfunc i₀} {iu} Ec
      e₀ : Ix._≈_ (μ τμ) b i
      e₀ = Ix.trans (μ τμ) {b} {roll-mor τμ .idxf .sfunc iu} {i} Er (idx-eq (roll-unroll τμ) i)

  module PairShape {Γ} (τ₀ : type 1) (σr : type 0) (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ₁ σ₂ : type 1) where
    τ× = (σ₁ [×] σ₂) [ σr ]
    τμ = (σ₁ [×] σ₂) [ μ τ₀ ]
    F× = fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm
    F₁ = fold-map τ₀ σr σ₁ ⟦ s ⟧tm
    F₂ = fold-map τ₀ σr σ₂ ⟦ s ⟧tm

    module Idx (gi : IxC Γ) (i : Ix ((σ₁ [×] σ₂) [ μ τ₀ ])) where
      i₁ = proj₁ i
      i₂ = proj₂ i
      I× = F× .idxf .sfunc (gi , i)
      I₁ = F₁ .idxf .sfunc (gi , i₁)
      I₂ = F₂ .idxf .sfunc (gi , i₂)
      E : Ix._≈_ τ× I× (I₁ , I₂)
      E = pair-idx {τ₀ = τ₀} s σ₁ σ₂ gi i

  mu-idx : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (τ' : type 2) gi (i : Ix ((μ τ') [ μ τ₀ ])) →
           let τμ = τ' [ μ τ₀ ]₁
               τₛ = τ' [ σr ]₁
               i₀ = ty-cast (sym (unfold₁-inst τ' (μ τ₀))) .idxf .sfunc (unroll-mor τμ .idxf .sfunc i)
           in
           Ix._≈_ (τₛ [ μ τₛ ])
             (ty-cast (unfold₁-inst τ' σr) .idxf .sfunc (fold-map τ₀ σr (unfold₁ τ') ⟦ s ⟧tm .idxf .sfunc (gi , i₀)))
             (unroll-mor τₛ .idxf .sfunc (fold-map τ₀ σr (μ τ') ⟦ s ⟧tm .idxf .sfunc (gi , i)))
  mu-idx {Γ} {τ₀} {σr} s τ' gi i =
    Ix.trans (τₛ [ μ τₛ ]) (Ix.sym (τₛ [ μ τₛ ]) (idx-eq (unroll-roll τₛ) a))
      (unroll-mor τₛ .idxf .sfunc-resp-≈ {roll-mor τₛ .idxf .sfunc a} {Fμ .idxf .sfunc (gi , i)} e₁)
    where
    open MuShape τ₀ σr s τ'
    open Idx gi i
    e₁ : Ix._≈_ (μ τₛ) (roll-mor τₛ .idxf .sfunc a) (Fμ .idxf .sfunc (gi , i))
    e₁ = Ix.trans (μ τₛ) {roll-mor τₛ .idxf .sfunc a} {Fμ .idxf .sfunc (gi , b)} {Fμ .idxf .sfunc (gi , i)}
           (Ix.sym (μ τₛ) {Fμ .idxf .sfunc (gi , b)} {roll-mor τₛ .idxf .sfunc a}
             (idx-eq (fold-map-mu τ₀ σr τ' ⟦ s ⟧tm) (gi , i₀)))
           (Fμ .idxf .sfunc-resp-≈ {gi , b} {gi , i} (IxC.refl Γ {gi} , e₀))

map-val : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
          (IH : ∀ {w' u T} (D : γ · w' , s ⇓ u [ T ]) {gj} (rγ : EnvValRel (γ · w') gj) →
                ValRel σr u (⟦ s ⟧tm .idxf .sfunc gj))
          {σ' : type 1} {v v' F} (M : Map γ s σ' v v' F) {gi} (rγ : EnvValRel γ gi) {i} →
          ValRel (σ' [ μ τ₀ ]) v i → ValRel (σ' [ σr ]) v' (fold-map τ₀ σr σ' ⟦ s ⟧tm .idxf .sfunc (gi , i))
map-val {τ₀ = τ₀} {σr} {s} IH (m-rec M D) {gi} rγ {i} r =
  ValRel-resp σr (rec-idx {τ₀ = τ₀} s gi i) (IH D (rγ · map-val IH M rγ (ValRel-at-bound (τ₀ [ μ τ₀ ]) r)))
map-val {τ₀ = τ₀} {σr} {s} IH (m-unit {v = v}) {gi} rγ {i} r =
  ValRel-resp unit {v} {i} {fold-map τ₀ σr unit ⟦ s ⟧tm .idxf .sfunc (gi , i)} (Ix.sym unit {fold-map τ₀ σr unit ⟦ s ⟧tm .idxf .sfunc (gi , i)} {i} (idx-eq (fold-map-unit τ₀ σr ⟦ s ⟧tm) (gi , i))) r
map-val {τ₀ = τ₀} {σr} {s} IH (m-base {b = b} {v = v}) {gi} rγ {i} r =
  ValRel-resp (base b) {v} {i} {fold-map τ₀ σr (base b) ⟦ s ⟧tm .idxf .sfunc (gi , i)} (Ix.sym (base b) {fold-map τ₀ σr (base b) ⟦ s ⟧tm .idxf .sfunc (gi , i)} {i} (idx-eq (fold-map-base τ₀ σr b ⟦ s ⟧tm) (gi , i))) r
map-val {τ₀ = τ₀} {σr} {s} IH (m-arrow {σ₁ = σ₁} {σ₂ = σ₂} {v = v}) {gi} rγ {i} r =
  ValRel-resp (σ₁ [→] σ₂) {v} {i} {fold-map τ₀ σr (σ₁ [→] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)}
    (Ix.sym (σ₁ [→] σ₂) {fold-map τ₀ σr (σ₁ [→] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)} {i} (idx-eq (fold-map-arrow τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i))) r
map-val {τ₀ = τ₀} {σr} {s} IH (m-inl {σ₁ = σ₁} {σ₂ = σ₂} M) {gi} rγ {i} (i' , r , ⟪ e₀ ⟫) =
  fold-map τ₀ σr σ₁ ⟦ s ⟧tm .idxf .sfunc (gi , i') ,
  ValRel-at-bound (σ₁ [ σr ]) (map-val IH M rγ (ValRel-at-bound (σ₁ [ μ τ₀ ]) r)) ,
  ⟪ inl-idx {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀ ⟫
map-val {τ₀ = τ₀} {σr} {s} IH (m-inr {σ₁ = σ₁} {σ₂ = σ₂} M) {gi} rγ {i} (i' , r , ⟪ e₀ ⟫) =
  fold-map τ₀ σr σ₂ ⟦ s ⟧tm .idxf .sfunc (gi , i') ,
  ValRel-at-bound (σ₂ [ σr ]) (map-val IH M rγ (ValRel-at-bound (σ₂ [ μ τ₀ ]) r)) ,
  ⟪ inr-idx {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀ ⟫
map-val {τ₀ = τ₀} {σr} {s} IH (m-pair {σ₁ = σ₁} {σ₂ = σ₂} M₁ M₂) {gi} rγ {i} (r₁ , r₂) =
  ValRel-at-bound (σ₁ [ σr ]) (ValRel-resp (σ₁ [ σr ]) (proj₁ e) (map-val IH M₁ rγ (ValRel-at-bound (σ₁ [ μ τ₀ ]) r₁))) ,
  ValRel-at-bound (σ₂ [ σr ]) (ValRel-resp (σ₂ [ σr ]) (proj₂ e) (map-val IH M₂ rγ (ValRel-at-bound (σ₂ [ μ τ₀ ]) r₂)))
  where
  e = Ix.sym ((σ₁ [×] σ₂) [ σr ])
        {fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)}
        {fold-map τ₀ σr σ₁ ⟦ s ⟧tm .idxf .sfunc (gi , proj₁ i) , fold-map τ₀ σr σ₂ ⟦ s ⟧tm .idxf .sfunc (gi , proj₂ i)}
        (pair-idx {τ₀ = τ₀} s σ₁ σ₂ gi i)
map-val {τ₀ = τ₀} {σr} {s} IH (m-mu {τ' = τ'} M) {gi} rγ {i} r =
  ValRel-at-bound (τₛ [ μ τₛ ])
    (ValRel-resp (τₛ [ μ τₛ ]) (mu-idx {τ₀ = τ₀} s τ' gi i)
      (ValRel-cast (unfold₁-inst τ' σr)
        (map-val IH M rγ (ValRel-cast⁻ (unfold₁-inst τ' (μ τ₀)) (ValRel-at-bound (τμ [ μ τμ ]) r)))))
  where open MuShape τ₀ σr s τ'

map-dep-leaf : ∀ {Γ} {γ : Env Γ} τ {v : Val τ} {i I' : Ix τ} (r : ValRel τ v i) (E : Ix._≈_ τ I' i)
               w (x : ∣ 𝔽 (width-env γ) ∣) (o : ∣ 𝔽 (width v) ∣) {e : ∣ Fib τ i ∣} {d : ∣ Fib τ I' ∣} →
               Fib._≈_ τ i (⟦ τ ⟧ .fam .subst E .func d) e →
               DepRel τ r o (Fib._+_ τ i (ctrl-dep-at τ i w) e) →
               DepRel τ (ValRel-resp τ (Ix.sym τ E) r) (ap (map-leaf γ (width v)) (map-input γ w x o))
                 (Fib._+_ τ I' (ctrl-dep-at τ I' w) d)
map-dep-leaf {γ = γ} τ {v} {i} {I'} r E w x o {e} {d} ed h =
  DepRel-transport⁻ τ E r
    (Fib.trans τ i (subst-ctrl-dep+ τ E w d) (Fib.+-cong τ i (Fib.refl τ i) ed))
    (DepRel-resp τ r (λ k → ≈-sym (ap-p₂-++ (inputs γ w x) o k)) (Fib.refl τ i) h)

private
  rec-fibre : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) gi (i : Ix (μ τ₀))
              (g : ∣ FibC Γ gi ∣) (e : ∣ Fib (μ τ₀) i ∣) →
              let i₀ = unroll-mor τ₀ .idxf .sfunc i
                  Fτ = fold-map τ₀ σr τ₀ ⟦ s ⟧tm
                  Fv = fold-map τ₀ σr (var zero) ⟦ s ⟧tm
              in
              Fib._≈_ σr (Fv .idxf .sfunc (gi , i))
                (⟦ σr ⟧ .fam .subst (rec-idx {τ₀ = τ₀} s gi i) .func
                  (⟦ s ⟧tm .famf .transf (gi , Fτ .idxf .sfunc (gi , i₀)) .func
                    (g , Fτ .famf .transf (gi , i₀) .func (g , unroll-mor τ₀ .famf .transf i .func e))))
                (Fv .famf .transf (gi , i) .func (g , e))
  rec-fibre {Γ} {τ₀} {σr} s gi i g e =
    Fib.trans σr I' (subst-trans ⟦ σr ⟧ {J} {Iᵣ'} {I'} E₁ E₂ Y)
    (Fib.trans σr I' (⟦ σr ⟧ .fam .subst {Iᵣ'} {I'} E₂ .func-resp-≈ step₁)
    (Fib.trans σr I' (Fib.sym σr I' (transf-natural {Dom} {⟦ σr ⟧} Fv {gi , Iᵣ} {gi , i} Eᵣ Xin))
      (Fv .famf .transf (gi , i) .func-resp-≈ step₂)))
    where
    i₀ = unroll-mor τ₀ .idxf .sfunc i
    e₀ = unroll-mor τ₀ .famf .transf i .func e
    Fτ = fold-map τ₀ σr τ₀ ⟦ s ⟧tm
    Fv = fold-map τ₀ σr (var zero) ⟦ s ⟧tm
    Dom = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ μ τ₀ ⟧
    Dom₀ = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ τ₀ [ μ τ₀ ] ⟧
    Dom' = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ τ₀ [ σr ] ⟧
    IF = Fτ .idxf .sfunc (gi , i₀)
    J = ⟦ s ⟧tm .idxf .sfunc (gi , IF)
    Iᵣ = roll-mor τ₀ .idxf .sfunc i₀
    Iᵣ' = Fv .idxf .sfunc (gi , Iᵣ)
    I' = Fv .idxf .sfunc (gi , i)
    dF = Fτ .famf .transf (gi , i₀) .func (g , e₀)
    Y = ⟦ s ⟧tm .famf .transf (gi , IF) .func (g , dF)
    P = Fam-P.pair {Dom₀} {⟦ Γ ⟧ctxt} {⟦ μ τ₀ ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {⟦ τ₀ [ μ τ₀ ] ⟧}) (Fam-cat._∘_ (roll-mor τ₀) (Fam-P.p₂ {⟦ Γ ⟧ctxt} {⟦ τ₀ [ μ τ₀ ] ⟧}))
    Xin = (g , roll-mor τ₀ .famf .transf i₀ .func e₀)
    X₀ = Fv .famf .transf (gi , Iᵣ) .func (P .famf .transf (gi , i₀) .func (g , e₀))
    X = Fv .famf .transf (gi , Iᵣ) .func Xin
    E₀ : Ix._≈_ σr Iᵣ' J
    E₀ = idx-eq (fold-map-rec τ₀ σr ⟦ s ⟧tm) (gi , i₀)
    E₁ : Ix._≈_ σr J Iᵣ'
    E₁ = Ix.sym σr {Iᵣ'} {J} E₀
    Eᵣ : IxO._≈_ Dom (gi , Iᵣ) (gi , i)
    Eᵣ = IxC.refl Γ {gi} , idx-eq (roll-unroll τ₀) i
    E₂ : Ix._≈_ σr Iᵣ' I'
    E₂ = Fv .idxf .sfunc-resp-≈ {gi , Iᵣ} {gi , i} Eᵣ
    step₁ : Fib._≈_ σr Iᵣ' (⟦ σr ⟧ .fam .subst {J} {Iᵣ'} E₁ .func Y) X
    step₁ =
      Fib.trans σr Iᵣ' (⟦ σr ⟧ .fam .subst {J} {Iᵣ'} E₁ .func-resp-≈
                          (Fib.trans σr J (⟦ s ⟧tm .famf .transf (gi , IF) .func-resp-≈
                                             (FibO.sym Dom' (gi , IF)
                                                (Fpair-elt {Dom₀} {⟦ Γ ⟧ctxt} {⟦ τ₀ [ σr ] ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {⟦ τ₀ [ μ τ₀ ] ⟧}) Fτ (gi , i₀) (g , e₀))))
                                          (Fib.sym σr J (fam-eq (fold-map-rec τ₀ σr ⟦ s ⟧tm) (gi , i₀) (g , e₀)))))
      (Fib.trans σr Iᵣ' (Fib.sym σr Iᵣ' (subst-trans ⟦ σr ⟧ {Iᵣ'} {J} {Iᵣ'} E₀ E₁ X₀))
      (Fib.trans σr Iᵣ' (subst-refl ⟦ σr ⟧ {Iᵣ'} (Ix.trans σr {Iᵣ'} {J} {Iᵣ'} E₀ E₁) X₀)
        (Fv .famf .transf (gi , Iᵣ) .func-resp-≈
           (Fpair-elt {Dom₀} {⟦ Γ ⟧ctxt} {⟦ μ τ₀ ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {⟦ τ₀ [ μ τ₀ ] ⟧}) (Fam-cat._∘_ (roll-mor τ₀) (Fam-P.p₂ {⟦ Γ ⟧ctxt} {⟦ τ₀ [ μ τ₀ ] ⟧})) (gi , i₀) (g , e₀)))))
    step₂ : FibO._≈_ Dom (gi , i) (Dom .fam .subst {gi , Iᵣ} {gi , i} Eᵣ .func Xin) (g , e)
    step₂ =
      FibO.trans Dom (gi , i)
        (Fprod-subst-elt {⟦ Γ ⟧ctxt} {⟦ μ τ₀ ⟧} {gi} {gi} {Iᵣ} {i} (IxC.refl Γ {gi}) (idx-eq (roll-unroll τ₀) i) g
           (roll-mor τ₀ .famf .transf i₀ .func e₀))
        (subst-refl ⟦ Γ ⟧ctxt {gi} (IxC.refl Γ {gi}) g , fam-eq (roll-unroll τ₀) i e)

map-dep-rec : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              (IHv : ∀ {w' u T} (D : γ · w' , s ⇓ u [ T ]) {gj} (rγ : EnvValRel (γ · w') gj) →
                     ValRel σr u (⟦ s ⟧tm .idxf .sfunc gj))
              {v v' u F T} (M : Map γ s τ₀ v v' F) (D : γ · v' , s ⇓ u [ T ]) {gi} (rγ : EnvValRel γ gi)
              {i} (r : ValRel (μ τ₀) (roll {τ₀} v) i) (w : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣)
              (g : ∣ FibC Γ gi ∣) → EnvDepRel rγ w x g →
              (∀ {i'} (r' : ValRel (τ₀ [ μ τ₀ ]) v i') (o : ∣ 𝔽 (width v) ∣) (e : ∣ Fib (τ₀ [ μ τ₀ ]) i' ∣) →
                 DepRel (τ₀ [ μ τ₀ ]) r' o (Fib._+_ (τ₀ [ μ τ₀ ]) i' (ctrl-dep-at (τ₀ [ μ τ₀ ]) i' w) e) →
                 DepRel (τ₀ [ σr ]) (map-val IHv M rγ r') (ap F (map-input γ w x o))
                   (Fib._+_ (τ₀ [ σr ]) (fold-map τ₀ σr τ₀ ⟦ s ⟧tm .idxf .sfunc (gi , i'))
                     (ctrl-dep-at (τ₀ [ σr ]) (fold-map τ₀ σr τ₀ ⟦ s ⟧tm .idxf .sfunc (gi , i')) w)
                     (fold-map τ₀ σr τ₀ ⟦ s ⟧tm .famf .transf (gi , i') .func (g , e)))) →
              (∀ {gj} (rγ' : EnvValRel (γ · v') gj) (x' : ∣ 𝔽 (width-env (γ · v')) ∣)
                 (g' : ∣ FibC (Γ ▸ τ₀ [ σr ]) gj ∣) → EnvDepRel rγ' w x' g' →
                 DepRel σr (IHv D rγ') (ap T (inputs (γ · v') w x'))
                   (Fib._+_ σr (⟦ s ⟧tm .idxf .sfunc gj) (ctrl-dep-at σr (⟦ s ⟧tm .idxf .sfunc gj) w)
                     (⟦ s ⟧tm .famf .transf gj .func g'))) →
              (o : ∣ 𝔽 (width v) ∣) (e : ∣ Fib (μ τ₀) i ∣) →
              DepRel (μ τ₀) {roll {τ₀} v} {i} r o (Fib._+_ (μ τ₀) i (ctrl-dep-at (μ τ₀) i w) e) →
              DepRel σr (map-val {s = s} IHv {var zero} (m-rec M D) rγ {i} r)
                (ap (T ∘ (rec-inputs γ v' ∘ ⟨ M.I , F ⟩)) (map-input γ w x o))
                (Fib._+_ σr (fold-map τ₀ σr (var zero) ⟦ s ⟧tm .idxf .sfunc (gi , i))
                  (ctrl-dep-at σr (fold-map τ₀ σr (var zero) ⟦ s ⟧tm .idxf .sfunc (gi , i)) w)
                  (fold-map τ₀ σr (var zero) ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)))
map-dep-rec {γ = γ} {τ₀} {σr} {s} IHv {v} {v'} {u} {F} {T} M D {gi} rγ {i} r w x g rel IHM IHD o e h =
  DepRel-resp σr (ValRel-resp σr (rec-idx {τ₀ = τ₀} s gi i) (IHv D rγ')) (λ k → ≈-sym (inputs-eq k))
    (Fib.trans σr I' (subst-ctrl-dep+ σr (rec-idx {τ₀ = τ₀} s gi i) w (⟦ s ⟧tm .famf .transf (gi , IF) .func (g , dF)))
      (Fib.+-cong σr I' (Fib.refl σr I') (rec-fibre {τ₀ = τ₀} s gi i g e)))
    (DepRel-transport σr (rec-idx {τ₀ = τ₀} s gi i) (IHv D rγ') (IHD rγ' x' (g , dF) rel'))
  where
  i₀ = unroll-mor τ₀ .idxf .sfunc i
  r₀ = ValRel-at-bound (τ₀ [ μ τ₀ ]) r
  e₀ = unroll-mor τ₀ .famf .transf i .func e
  Fτ = fold-map τ₀ σr τ₀ ⟦ s ⟧tm
  IF = Fτ .idxf .sfunc (gi , i₀)
  I' = fold-map τ₀ σr (var zero) ⟦ s ⟧tm .idxf .sfunc (gi , i)
  rv' = map-val IHv M rγ r₀
  rγ' = rγ · rv'
  y = map-input γ w x o
  oF = ap F y
  dF = Fτ .famf .transf (gi , i₀) .func (g , e₀)
  x' : ∣ 𝔽 (width-env γ + width v') ∣
  x' l = ap (M.in₁ {width-env γ} {width v'}) x l +ₛ ap (M.in₂ {width-env γ} {width v'}) oF l
  h₀ : DepRel (τ₀ [ μ τ₀ ]) r₀ o (Fib._+_ (τ₀ [ μ τ₀ ]) i₀ (ctrl-dep-at (τ₀ [ μ τ₀ ]) i₀ w) e₀)
  h₀ = DepRel-resp (τ₀ [ μ τ₀ ]) r₀ (λ k → ≈-refl)
         (Fib.trans (τ₀ [ μ τ₀ ]) i₀
           (unroll-mor τ₀ .famf .transf i .preserve-+ {ctrl-dep-at (μ τ₀) i w} {e})
           (Fib.+-cong (τ₀ [ μ τ₀ ]) i₀ (preserves-unroll-ctrl-dep τ₀ .at i .func-eq {w} {w} ≈-refl)
                                       (Fib.refl (τ₀ [ μ τ₀ ]) i₀)))
         (DepRel-at-bound (τ₀ [ μ τ₀ ]) r h)
  rel' : EnvDepRel rγ' w x' (g , dF)
  rel' = EnvDepRel-resp rγ w (λ k → ≈-sym (ap-p₁-++ x oF k)) rel ,
         (ctrl-dep-at (τ₀ [ σr ]) IF w ,
          (Fib.⊑-refl (τ₀ [ σr ]) IF ,
           DepRel-resp (τ₀ [ σr ]) rv' (λ k → ≈-sym (ap-p₂-++ x oF k)) (Fib.+-comm (τ₀ [ σr ]) IF)
             (IHM r₀ o e₀ h₀)))
  inputs-eq : ∀ k → ap (T ∘ (rec-inputs γ v' ∘ ⟨ M.I , F ⟩)) y k ≈s ap T (inputs (γ · v') w x') k
  inputs-eq k = ≈-trans (app-∘ T (rec-inputs γ v' ∘ ⟨ M.I , F ⟩) y k)
                        (app-congᵥ T (ap-rec-inputs γ {m = width v} v' F w x o) k)

private
  inl-fibre : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ₁ σ₂ : type 1) gi {i} {i' : Ix (σ₁ [ μ τ₀ ])}
              (e₀ : Ix._≈_ ((σ₁ [+] σ₂) [ μ τ₀ ]) i (inj₁ i')) (g : ∣ FibC Γ gi ∣) (e : ∣ Fib ((σ₁ [+] σ₂) [ μ τ₀ ]) i ∣) →
              let F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
                  F₁ = fold-map τ₀ σr σ₁ ⟦ s ⟧tm
                  ẽ = ⟦ (σ₁ [+] σ₂) [ μ τ₀ ] ⟧ .fam .subst {i} {inj₁ i'} e₀ .func e
              in
              Fib._≈_ ((σ₁ [+] σ₂) [ σr ]) (inj₁ (F₁ .idxf .sfunc (gi , i')))
                (⟦ (σ₁ [+] σ₂) [ σr ] ⟧ .fam .subst {F₊ .idxf .sfunc (gi , i)} {inj₁ (F₁ .idxf .sfunc (gi , i'))}
                   (inl-idx {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀) .func
                  (F₊ .famf .transf (gi , i) .func (g , e)))
                (proj₁ ẽ , F₁ .famf .transf (gi , i') .func (g , proj₂ ẽ))
  inl-fibre {Γ} {τ₀} {σr} s σ₁ σ₂ gi {i} {i'} e₀ g e =
    Fib.trans τ₊ J (subst-trans ⟦ τ₊ ⟧ {I₊} {I₊'} {J} E₁ E₂ (F₊ .famf .transf (gi , i) .func (g , e)))
    (Fib.trans τ₊ J (⟦ τ₊ ⟧ .fam .subst {I₊'} {J} E₂ .func-resp-≈
                       (Fib.trans τ₊ I₊' step₁ (F₊ .famf .transf (gi , inj₁ i') .func-resp-≈ step₂)))
    (Fib.trans τ₊ J (fam-eq (fold-map-inl-L τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i') (g , ẽ))
    (Fib.trans τ₊ J (strong-Lf-map-transf F₁ {gi} {i'} .func-eq (FibO.refl Domₖ (gi , i') {g , ẽ}))
      (strong-Lmap-elt (F₁ .famf .transf (gi , i')) g (proj₁ ẽ) (proj₂ ẽ)))))
    where
    τ₊ = (σ₁ [+] σ₂) [ σr ]
    τμ = (σ₁ [+] σ₂) [ μ τ₀ ]
    F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
    F₁ = fold-map τ₀ σr σ₁ ⟦ s ⟧tm
    Dom = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ τμ ⟧
    Domₖ = Fam-P.prod ⟦ Γ ⟧ctxt (Lf ⟦ σ₁ [ μ τ₀ ] ⟧)
    ẽ = ⟦ τμ ⟧ .fam .subst {i} {inj₁ i'} e₀ .func e
    I₊ = F₊ .idxf .sfunc (gi , i)
    I₊' = F₊ .idxf .sfunc (gi , inj₁ i')
    J = inj₁ (F₁ .idxf .sfunc (gi , i'))
    Eᵢ : IxO._≈_ Dom (gi , i) (gi , inj₁ i')
    Eᵢ = IxC.refl Γ {gi} , e₀
    E₁ : Ix._≈_ τ₊ I₊ I₊'
    E₁ = F₊ .idxf .sfunc-resp-≈ {gi , i} {gi , inj₁ i'} Eᵢ
    E₂ : Ix._≈_ τ₊ I₊' J
    E₂ = idx-eq (fold-map-inl-L τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i')
    P = Fam-P.pair {Domₖ} {⟦ Γ ⟧ctxt} {⟦ τμ ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Lf ⟦ σ₁ [ μ τ₀ ] ⟧})
          (Fam-cat._∘_ in₁ (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Lf ⟦ σ₁ [ μ τ₀ ] ⟧}))
    step₁ : Fib._≈_ τ₊ I₊' (⟦ τ₊ ⟧ .fam .subst {I₊} {I₊'} E₁ .func (F₊ .famf .transf (gi , i) .func (g , e)))
                           (F₊ .famf .transf (gi , inj₁ i') .func (Dom .fam .subst {gi , i} {gi , inj₁ i'} Eᵢ .func (g , e)))
    step₁ = Fib.sym τ₊ I₊' (transf-natural {Dom} {⟦ τ₊ ⟧} F₊ {gi , i} {gi , inj₁ i'} Eᵢ (g , e))
    step₂ : FibO._≈_ Dom (gi , inj₁ i')
              (Dom .fam .subst {gi , i} {gi , inj₁ i'} Eᵢ .func (g , e)) (P .famf .transf (gi , i') .func (g , ẽ))
    step₂ = FibO.trans Dom (gi , inj₁ i')
              (Fprod-subst-elt {⟦ Γ ⟧ctxt} {⟦ τμ ⟧} {gi} {gi} {i} {inj₁ i'} (IxC.refl Γ {gi}) e₀ g e)
              (FibO.trans Dom (gi , inj₁ i')
                 (subst-refl ⟦ Γ ⟧ctxt {gi} (IxC.refl Γ {gi}) g , Fib.refl τμ (inj₁ i') {ẽ})
                 (FibO.sym Dom (gi , inj₁ i')
                    (Fpair-elt {Domₖ} {⟦ Γ ⟧ctxt} {⟦ τμ ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Lf ⟦ σ₁ [ μ τ₀ ] ⟧})
                       (Fam-cat._∘_ in₁ (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Lf ⟦ σ₁ [ μ τ₀ ] ⟧})) (gi , i') (g , ẽ))))

  inr-fibre : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ₁ σ₂ : type 1) gi {i} {i' : Ix (σ₂ [ μ τ₀ ])}
              (e₀ : Ix._≈_ ((σ₁ [+] σ₂) [ μ τ₀ ]) i (inj₂ i')) (g : ∣ FibC Γ gi ∣) (e : ∣ Fib ((σ₁ [+] σ₂) [ μ τ₀ ]) i ∣) →
              let F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
                  F₂ = fold-map τ₀ σr σ₂ ⟦ s ⟧tm
                  ẽ = ⟦ (σ₁ [+] σ₂) [ μ τ₀ ] ⟧ .fam .subst {i} {inj₂ i'} e₀ .func e
              in
              Fib._≈_ ((σ₁ [+] σ₂) [ σr ]) (inj₂ (F₂ .idxf .sfunc (gi , i')))
                (⟦ (σ₁ [+] σ₂) [ σr ] ⟧ .fam .subst {F₊ .idxf .sfunc (gi , i)} {inj₂ (F₂ .idxf .sfunc (gi , i'))}
                   (inr-idx {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀) .func
                  (F₊ .famf .transf (gi , i) .func (g , e)))
                (proj₁ ẽ , F₂ .famf .transf (gi , i') .func (g , proj₂ ẽ))
  inr-fibre {Γ} {τ₀} {σr} s σ₁ σ₂ gi {i} {i'} e₀ g e =
    Fib.trans τ₊ J (subst-trans ⟦ τ₊ ⟧ {I₊} {I₊'} {J} E₁ E₂ (F₊ .famf .transf (gi , i) .func (g , e)))
    (Fib.trans τ₊ J (⟦ τ₊ ⟧ .fam .subst {I₊'} {J} E₂ .func-resp-≈
                       (Fib.trans τ₊ I₊' step₁ (F₊ .famf .transf (gi , inj₂ i') .func-resp-≈ step₂)))
    (Fib.trans τ₊ J (fam-eq (fold-map-inr-L τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i') (g , ẽ))
    (Fib.trans τ₊ J (strong-Lf-map-transf F₂ {gi} {i'} .func-eq (FibO.refl Domₖ (gi , i') {g , ẽ}))
      (strong-Lmap-elt (F₂ .famf .transf (gi , i')) g (proj₁ ẽ) (proj₂ ẽ)))))
    where
    τ₊ = (σ₁ [+] σ₂) [ σr ]
    τμ = (σ₁ [+] σ₂) [ μ τ₀ ]
    F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
    F₂ = fold-map τ₀ σr σ₂ ⟦ s ⟧tm
    Dom = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ τμ ⟧
    Domₖ = Fam-P.prod ⟦ Γ ⟧ctxt (Lf ⟦ σ₂ [ μ τ₀ ] ⟧)
    ẽ = ⟦ τμ ⟧ .fam .subst {i} {inj₂ i'} e₀ .func e
    I₊ = F₊ .idxf .sfunc (gi , i)
    I₊' = F₊ .idxf .sfunc (gi , inj₂ i')
    J = inj₂ (F₂ .idxf .sfunc (gi , i'))
    Eᵢ : IxO._≈_ Dom (gi , i) (gi , inj₂ i')
    Eᵢ = IxC.refl Γ {gi} , e₀
    E₁ : Ix._≈_ τ₊ I₊ I₊'
    E₁ = F₊ .idxf .sfunc-resp-≈ {gi , i} {gi , inj₂ i'} Eᵢ
    E₂ : Ix._≈_ τ₊ I₊' J
    E₂ = idx-eq (fold-map-inr-L τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i')
    P = Fam-P.pair {Domₖ} {⟦ Γ ⟧ctxt} {⟦ τμ ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Lf ⟦ σ₂ [ μ τ₀ ] ⟧})
          (Fam-cat._∘_ in₂ (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Lf ⟦ σ₂ [ μ τ₀ ] ⟧}))
    step₁ : Fib._≈_ τ₊ I₊' (⟦ τ₊ ⟧ .fam .subst {I₊} {I₊'} E₁ .func (F₊ .famf .transf (gi , i) .func (g , e)))
                           (F₊ .famf .transf (gi , inj₂ i') .func (Dom .fam .subst {gi , i} {gi , inj₂ i'} Eᵢ .func (g , e)))
    step₁ = Fib.sym τ₊ I₊' (transf-natural {Dom} {⟦ τ₊ ⟧} F₊ {gi , i} {gi , inj₂ i'} Eᵢ (g , e))
    step₂ : FibO._≈_ Dom (gi , inj₂ i')
              (Dom .fam .subst {gi , i} {gi , inj₂ i'} Eᵢ .func (g , e)) (P .famf .transf (gi , i') .func (g , ẽ))
    step₂ = FibO.trans Dom (gi , inj₂ i')
              (Fprod-subst-elt {⟦ Γ ⟧ctxt} {⟦ τμ ⟧} {gi} {gi} {i} {inj₂ i'} (IxC.refl Γ {gi}) e₀ g e)
              (FibO.trans Dom (gi , inj₂ i')
                 (subst-refl ⟦ Γ ⟧ctxt {gi} (IxC.refl Γ {gi}) g , Fib.refl τμ (inj₂ i') {ẽ})
                 (FibO.sym Dom (gi , inj₂ i')
                    (Fpair-elt {Domₖ} {⟦ Γ ⟧ctxt} {⟦ τμ ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Lf ⟦ σ₂ [ μ τ₀ ] ⟧})
                       (Fam-cat._∘_ in₂ (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Lf ⟦ σ₂ [ μ τ₀ ] ⟧})) (gi , i') (g , ẽ))))

map-built-suc : ∀ {Γ} (γ : Env Γ) {m n} (F : M.Matrix n (suc (width-env γ) + m)) w x (o : ∣ 𝔽 (suc m) ∣) k →
                ap (map-built-out γ m n M.+ₘ (M.in₂ {1} ∘ (F ∘ sub-inputs γ (M.p₂ {1} {m})))) (map-input γ w x o) (suc k)
                  ≈s ap F (map-input γ w x (λ k → o (suc k))) k
map-built-suc γ {m} F w x o k =
  ≈-trans (map-built γ (F ∘ sub-inputs γ (M.p₂ {1} {m})) w x o (suc k))
  (≈-trans (app-∘ F (sub-inputs γ (M.p₂ {1} {m})) (map-input γ w x o) k)
    (app-congᵥ F (λ l → ≈-trans (ap-sub-inputs γ (M.p₂ {1} {m}) w x o l)
                                (+-cong ≈-refl (app-congᵥ (M.in₂ {suc (width-env γ)} {m}) (ap-p₂₁ o) l))) k))

map-dep-inl : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              (IHv : ∀ {w' u T} (D : γ · w' , s ⇓ u [ T ]) {gj} (rγ : EnvValRel (γ · w') gj) →
                     ValRel σr u (⟦ s ⟧tm .idxf .sfunc gj))
              {σ₁ σ₂ : type 1} {v v' F} (M : Map γ s σ₁ v v' F) {gi} (rγ : EnvValRel γ gi)
              {i} (r : ValRel ((σ₁ [+] σ₂) [ μ τ₀ ]) (inl {τ₂ = σ₂ [ μ τ₀ ]} v) i) (w : Setoid.Carrier A)
              (x : ∣ 𝔽 (width-env γ) ∣) (g : ∣ FibC Γ gi ∣) →
              (∀ {i'} (r' : ValRel (σ₁ [ μ τ₀ ]) v i') (o : ∣ 𝔽 (width v) ∣) (e : ∣ Fib (σ₁ [ μ τ₀ ]) i' ∣) →
                 DepRel (σ₁ [ μ τ₀ ]) r' o (Fib._+_ (σ₁ [ μ τ₀ ]) i' (ctrl-dep-at (σ₁ [ μ τ₀ ]) i' w) e) →
                 DepRel (σ₁ [ σr ]) (map-val IHv M rγ r') (ap F (map-input γ w x o))
                   (Fib._+_ (σ₁ [ σr ]) (fold-map τ₀ σr σ₁ ⟦ s ⟧tm .idxf .sfunc (gi , i'))
                     (ctrl-dep-at (σ₁ [ σr ]) (fold-map τ₀ σr σ₁ ⟦ s ⟧tm .idxf .sfunc (gi , i')) w)
                     (fold-map τ₀ σr σ₁ ⟦ s ⟧tm .famf .transf (gi , i') .func (g , e)))) →
              (o : ∣ 𝔽 (suc (width v)) ∣) (e : ∣ Fib ((σ₁ [+] σ₂) [ μ τ₀ ]) i ∣) →
              DepRel ((σ₁ [+] σ₂) [ μ τ₀ ]) {inl {τ₂ = σ₂ [ μ τ₀ ]} v} {i} r o
                (Fib._+_ ((σ₁ [+] σ₂) [ μ τ₀ ]) i (ctrl-dep-at ((σ₁ [+] σ₂) [ μ τ₀ ]) i w) e) →
              DepRel ((σ₁ [+] σ₂) [ σr ]) {inl {τ₂ = σ₂ [ σr ]} v'} {fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)}
                (map-val {s = s} IHv {σ₁ [+] σ₂} (m-inl M) rγ {i} r)
                (ap (map-built-out γ (width v) (width v') M.+ₘ (M.in₂ {1} ∘ (F ∘ sub-inputs γ (M.p₂ {1} {width v}))))
                    (map-input γ w x o))
                (Fib._+_ ((σ₁ [+] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i))
                  (ctrl-dep-at ((σ₁ [+] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)) w)
                  (fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)))
map-dep-inl {γ = γ} {τ₀} {σr} {s} IHv {σ₁} {σ₂} {v} {v'} {F} M {gi} rγ {i} (i' , r₁ , ⟪ e₀ ⟫) w x g IHM o e (h₀ , h₁) =
  root-eq ,
  DepRel-at-bound (σ₁ [ σr ]) rv'
    (DepRel-resp (σ₁ [ σr ]) rv' (λ k → ≈-sym (map-built-suc γ F w x o k)) payload-eq
      (IHM r₁' (λ k → o (suc k)) (proj₂ ẽ) h₁'))
  where
  τ₊ = (σ₁ [+] σ₂) [ σr ]
  τμ = (σ₁ [+] σ₂) [ μ τ₀ ]
  F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
  F₁ = fold-map τ₀ σr σ₁ ⟦ s ⟧tm
  r₁' = ValRel-at-bound (σ₁ [ μ τ₀ ]) r₁
  rv' = map-val IHv M rγ r₁'
  Iₖ = F₁ .idxf .sfunc (gi , i')
  I₊ = F₊ .idxf .sfunc (gi , i)
  E = inl-idx {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀
  ẽ = ⟦ τμ ⟧ .fam .subst {i} {inj₁ i'} e₀ .func e
  y = map-input γ w x o
  dF = F₊ .famf .transf (gi , i) .func (g , e)
  d'' = ⟦ τ₊ ⟧ .fam .subst {I₊} {inj₁ Iₖ} E .func (Fib._+_ τ₊ I₊ (ctrl-dep-at τ₊ I₊ w) dF)
  split' = subst-ctrl-dep+ τμ {i} {inj₁ i'} e₀ w e
  split'' = subst-ctrl-dep+ τ₊ {I₊} {inj₁ Iₖ} E w dF
  h₁' : DepRel (σ₁ [ μ τ₀ ]) r₁' (λ k → o (suc k))
          (Fib._+_ (σ₁ [ μ τ₀ ]) i' (ctrl-dep-at (σ₁ [ μ τ₀ ]) i' w) (proj₂ ẽ))
  h₁' = DepRel-resp (σ₁ [ μ τ₀ ]) r₁' (λ k → ≈-refl)
          (Fib.trans (σ₁ [ μ τ₀ ]) i' (proj₂ split')
             (Fib.+-cong (σ₁ [ μ τ₀ ]) i' (proj₂ (ctrl-dep-inj₁ {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} i' w)) (Fib.refl (σ₁ [ μ τ₀ ]) i')))
          (DepRel-at-bound (σ₁ [ μ τ₀ ]) r₁ h₁)
  root-eq : ap (map-built-out γ (width v) (width v') M.+ₘ (M.in₂ {1} ∘ (F ∘ sub-inputs γ (M.p₂ {1} {width v})))) y zero
            ≈s proj₁ d''
  root-eq =
    ≈-trans (map-built γ (F ∘ sub-inputs γ (M.p₂ {1} {width v})) w x o zero)
    (≈-trans (+-cong ≈-refl (≈-trans h₀ (≈-trans (proj₁ split')
                                                 (+-cong (proj₁ (ctrl-dep-inj₁ {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} i' w)) ≈-refl))))
    (≈-trans (≈-sym +-assoc)
    (≈-trans (+-cong (+-idem (ctrl ·ₛ w)) ≈-refl)
    (≈-sym (≈-trans (proj₁ split'')
                    (+-cong (proj₁ (ctrl-dep-inj₁ {σ₁ [ σr ]} {σ₂ [ σr ]} Iₖ w))
                            (proj₁ (inl-fibre {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀ g e))))))))
  payload-eq : Fib._≈_ (σ₁ [ σr ]) Iₖ
                 (Fib._+_ (σ₁ [ σr ]) Iₖ (ctrl-dep-at (σ₁ [ σr ]) Iₖ w) (F₁ .famf .transf (gi , i') .func (g , proj₂ ẽ)))
                 (proj₂ d'')
  payload-eq =
    Fib.sym (σ₁ [ σr ]) Iₖ
      (Fib.trans (σ₁ [ σr ]) Iₖ (proj₂ split'')
        (Fib.+-cong (σ₁ [ σr ]) Iₖ (proj₂ (ctrl-dep-inj₁ {σ₁ [ σr ]} {σ₂ [ σr ]} Iₖ w))
                                   (proj₂ (inl-fibre {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀ g e))))

map-dep-inr : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
              (IHv : ∀ {w' u T} (D : γ · w' , s ⇓ u [ T ]) {gj} (rγ : EnvValRel (γ · w') gj) →
                     ValRel σr u (⟦ s ⟧tm .idxf .sfunc gj))
              {σ₁ σ₂ : type 1} {v v' F} (M : Map γ s σ₂ v v' F) {gi} (rγ : EnvValRel γ gi)
              {i} (r : ValRel ((σ₁ [+] σ₂) [ μ τ₀ ]) (inr {τ₁ = σ₁ [ μ τ₀ ]} v) i) (w : Setoid.Carrier A)
              (x : ∣ 𝔽 (width-env γ) ∣) (g : ∣ FibC Γ gi ∣) →
              (∀ {i'} (r' : ValRel (σ₂ [ μ τ₀ ]) v i') (o : ∣ 𝔽 (width v) ∣) (e : ∣ Fib (σ₂ [ μ τ₀ ]) i' ∣) →
                 DepRel (σ₂ [ μ τ₀ ]) r' o (Fib._+_ (σ₂ [ μ τ₀ ]) i' (ctrl-dep-at (σ₂ [ μ τ₀ ]) i' w) e) →
                 DepRel (σ₂ [ σr ]) (map-val IHv M rγ r') (ap F (map-input γ w x o))
                   (Fib._+_ (σ₂ [ σr ]) (fold-map τ₀ σr σ₂ ⟦ s ⟧tm .idxf .sfunc (gi , i'))
                     (ctrl-dep-at (σ₂ [ σr ]) (fold-map τ₀ σr σ₂ ⟦ s ⟧tm .idxf .sfunc (gi , i')) w)
                     (fold-map τ₀ σr σ₂ ⟦ s ⟧tm .famf .transf (gi , i') .func (g , e)))) →
              (o : ∣ 𝔽 (suc (width v)) ∣) (e : ∣ Fib ((σ₁ [+] σ₂) [ μ τ₀ ]) i ∣) →
              DepRel ((σ₁ [+] σ₂) [ μ τ₀ ]) {inr {τ₁ = σ₁ [ μ τ₀ ]} v} {i} r o
                (Fib._+_ ((σ₁ [+] σ₂) [ μ τ₀ ]) i (ctrl-dep-at ((σ₁ [+] σ₂) [ μ τ₀ ]) i w) e) →
              DepRel ((σ₁ [+] σ₂) [ σr ]) {inr {τ₁ = σ₁ [ σr ]} v'} {fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)}
                (map-val {s = s} IHv {σ₁ [+] σ₂} (m-inr M) rγ {i} r)
                (ap (map-built-out γ (width v) (width v') M.+ₘ (M.in₂ {1} ∘ (F ∘ sub-inputs γ (M.p₂ {1} {width v}))))
                    (map-input γ w x o))
                (Fib._+_ ((σ₁ [+] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i))
                  (ctrl-dep-at ((σ₁ [+] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)) w)
                  (fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)))
map-dep-inr {γ = γ} {τ₀} {σr} {s} IHv {σ₁} {σ₂} {v} {v'} {F} M {gi} rγ {i} (i' , r₁ , ⟪ e₀ ⟫) w x g IHM o e (h₀ , h₁) =
  root-eq ,
  DepRel-at-bound (σ₂ [ σr ]) rv'
    (DepRel-resp (σ₂ [ σr ]) rv' (λ k → ≈-sym (map-built-suc γ F w x o k)) payload-eq
      (IHM r₁' (λ k → o (suc k)) (proj₂ ẽ) h₁'))
  where
  τ₊ = (σ₁ [+] σ₂) [ σr ]
  τμ = (σ₁ [+] σ₂) [ μ τ₀ ]
  F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
  F₂ = fold-map τ₀ σr σ₂ ⟦ s ⟧tm
  r₁' = ValRel-at-bound (σ₂ [ μ τ₀ ]) r₁
  rv' = map-val IHv M rγ r₁'
  Iₖ = F₂ .idxf .sfunc (gi , i')
  I₊ = F₊ .idxf .sfunc (gi , i)
  E = inr-idx {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀
  ẽ = ⟦ τμ ⟧ .fam .subst {i} {inj₂ i'} e₀ .func e
  y = map-input γ w x o
  dF = F₊ .famf .transf (gi , i) .func (g , e)
  d'' = ⟦ τ₊ ⟧ .fam .subst {I₊} {inj₂ Iₖ} E .func (Fib._+_ τ₊ I₊ (ctrl-dep-at τ₊ I₊ w) dF)
  split' = subst-ctrl-dep+ τμ {i} {inj₂ i'} e₀ w e
  split'' = subst-ctrl-dep+ τ₊ {I₊} {inj₂ Iₖ} E w dF
  h₁' : DepRel (σ₂ [ μ τ₀ ]) r₁' (λ k → o (suc k))
          (Fib._+_ (σ₂ [ μ τ₀ ]) i' (ctrl-dep-at (σ₂ [ μ τ₀ ]) i' w) (proj₂ ẽ))
  h₁' = DepRel-resp (σ₂ [ μ τ₀ ]) r₁' (λ k → ≈-refl)
          (Fib.trans (σ₂ [ μ τ₀ ]) i' (proj₂ split')
             (Fib.+-cong (σ₂ [ μ τ₀ ]) i' (proj₂ (ctrl-dep-inj₂ {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} i' w)) (Fib.refl (σ₂ [ μ τ₀ ]) i')))
          (DepRel-at-bound (σ₂ [ μ τ₀ ]) r₁ h₁)
  root-eq : ap (map-built-out γ (width v) (width v') M.+ₘ (M.in₂ {1} ∘ (F ∘ sub-inputs γ (M.p₂ {1} {width v})))) y zero
            ≈s proj₁ d''
  root-eq =
    ≈-trans (map-built γ (F ∘ sub-inputs γ (M.p₂ {1} {width v})) w x o zero)
    (≈-trans (+-cong ≈-refl (≈-trans h₀ (≈-trans (proj₁ split')
                                                 (+-cong (proj₁ (ctrl-dep-inj₂ {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} i' w)) ≈-refl))))
    (≈-trans (≈-sym +-assoc)
    (≈-trans (+-cong (+-idem (ctrl ·ₛ w)) ≈-refl)
    (≈-sym (≈-trans (proj₁ split'')
                    (+-cong (proj₁ (ctrl-dep-inj₂ {σ₁ [ σr ]} {σ₂ [ σr ]} Iₖ w))
                            (proj₁ (inr-fibre {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀ g e))))))))
  payload-eq : Fib._≈_ (σ₂ [ σr ]) Iₖ
                 (Fib._+_ (σ₂ [ σr ]) Iₖ (ctrl-dep-at (σ₂ [ σr ]) Iₖ w) (F₂ .famf .transf (gi , i') .func (g , proj₂ ẽ)))
                 (proj₂ d'')
  payload-eq =
    Fib.sym (σ₂ [ σr ]) Iₖ
      (Fib.trans (σ₂ [ σr ]) Iₖ (proj₂ split'')
        (Fib.+-cong (σ₂ [ σr ]) Iₖ (proj₂ (ctrl-dep-inj₂ {σ₁ [ σr ]} {σ₂ [ σr ]} Iₖ w))
                                   (proj₂ (inr-fibre {τ₀ = τ₀} s σ₁ σ₂ gi {i} {i'} e₀ g e))))

private
  pair-fibre : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (σ₁ σ₂ : type 1) gi
               (i : Ix ((σ₁ [×] σ₂) [ μ τ₀ ])) (g : ∣ FibC Γ gi ∣) (e : ∣ Fib ((σ₁ [×] σ₂) [ μ τ₀ ]) i ∣) →
               let F× = fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm
                   F₁ = fold-map τ₀ σr σ₁ ⟦ s ⟧tm
                   F₂ = fold-map τ₀ σr σ₂ ⟦ s ⟧tm
               in
               Fib._≈_ ((σ₁ [×] σ₂) [ σr ]) (F₁ .idxf .sfunc (gi , proj₁ i) , F₂ .idxf .sfunc (gi , proj₂ i))
                 (⟦ (σ₁ [×] σ₂) [ σr ] ⟧ .fam .subst {F× .idxf .sfunc (gi , i)}
                    {F₁ .idxf .sfunc (gi , proj₁ i) , F₂ .idxf .sfunc (gi , proj₂ i)}
                    (pair-idx {τ₀ = τ₀} s σ₁ σ₂ gi i) .func (F× .famf .transf (gi , i) .func (g , e)))
                 (proj₁ e , (F₁ .famf .transf (gi , proj₁ i) .func (g , proj₁ (proj₂ e)) ,
                            F₂ .famf .transf (gi , proj₂ i) .func (g , proj₂ (proj₂ e))))
  pair-fibre {Γ} {τ₀} {σr} s σ₁ σ₂ gi i g e =
    Fib.trans τ× J (fam-eq (fold-map-pair-L τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i) (g , e))
    (Fib.trans τ× J (strong-Lf-map-transf SP {gi} {i} .func-eq (FibO.refl Dom (gi , i) {g , e}))
    (Fib.trans τ× J (strong-Lmap-elt (SP .famf .transf (gi , i)) g (proj₁ e) (proj₂ e))
      (≈-refl , payload)))
    where
    open PairShape τ₀ σr s σ₁ σ₂
    open Idx gi i
    X₁ = ⟦ σ₁ [ μ τ₀ ] ⟧
    X₂ = ⟦ σ₂ [ μ τ₀ ] ⟧
    Y₁ = ⟦ σ₁ [ σr ] ⟧
    Y₂ = ⟦ σ₂ [ σr ] ⟧
    Dom = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ τμ ⟧
    Dom₀ = Fam-P.prod ⟦ Γ ⟧ctxt (Fam-P.prod X₁ X₂)
    J = (I₁ , I₂)
    SP = Fam-P.strong-prod-m {⟦ Γ ⟧ctxt} {X₁} {X₂} {Y₁} {Y₂} F₁ F₂
    SP₁ = Fam-P.strong-p₁ {⟦ Γ ⟧ctxt} {X₁} {X₂}
    SP₂ = Fam-P.strong-p₂ {⟦ Γ ⟧ctxt} {X₁} {X₂}
    payload : FibO._≈_ (Fam-P.prod Y₁ Y₂) J
                (SP .famf .transf (gi , i) .func (g , proj₂ e))
                (F₁ .famf .transf (gi , proj₁ i) .func (g , proj₁ (proj₂ e)) ,
                 F₂ .famf .transf (gi , proj₂ i) .func (g , proj₂ (proj₂ e)))
    payload =
      FibO.trans (Fam-P.prod Y₁ Y₂) J
        (Fpair-elt {Dom₀} {Y₁} {Y₂} (Fam-cat._∘_ F₁ SP₁) (Fam-cat._∘_ F₂ SP₂) (gi , i) (g , proj₂ e))
        (F₁ .famf .transf (gi , proj₁ i) .func-resp-≈
           (Fpair-elt {Dom₀} {⟦ Γ ⟧ctxt} {X₁} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Fam-P.prod X₁ X₂})
              (Fam-cat._∘_ (Fam-P.p₁ {X₁} {X₂}) (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Fam-P.prod X₁ X₂})) (gi , i) (g , proj₂ e)) ,
         F₂ .famf .transf (gi , proj₂ i) .func-resp-≈
           (Fpair-elt {Dom₀} {⟦ Γ ⟧ctxt} {X₂} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Fam-P.prod X₁ X₂})
              (Fam-cat._∘_ (Fam-P.p₂ {X₁} {X₂}) (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Fam-P.prod X₁ X₂})) (gi , i) (g , proj₂ e)))

map-dep-pair : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
               (IHv : ∀ {w' u T} (D : γ · w' , s ⇓ u [ T ]) {gj} (rγ : EnvValRel (γ · w') gj) →
                      ValRel σr u (⟦ s ⟧tm .idxf .sfunc gj))
               {σ₁ σ₂ : type 1} {v v' u u' F G} (M₁ : Map γ s σ₁ v v' F) (M₂ : Map γ s σ₂ u u' G)
               {gi} (rγ : EnvValRel γ gi) {i} (r : ValRel ((σ₁ [×] σ₂) [ μ τ₀ ]) (pair v u) i)
               (w : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣) (g : ∣ FibC Γ gi ∣) →
               (∀ {i'} (r' : ValRel (σ₁ [ μ τ₀ ]) v i') (o : ∣ 𝔽 (width v) ∣) (e : ∣ Fib (σ₁ [ μ τ₀ ]) i' ∣) →
                  DepRel (σ₁ [ μ τ₀ ]) r' o (Fib._+_ (σ₁ [ μ τ₀ ]) i' (ctrl-dep-at (σ₁ [ μ τ₀ ]) i' w) e) →
                  DepRel (σ₁ [ σr ]) (map-val IHv M₁ rγ r') (ap F (map-input γ w x o))
                    (Fib._+_ (σ₁ [ σr ]) (fold-map τ₀ σr σ₁ ⟦ s ⟧tm .idxf .sfunc (gi , i'))
                      (ctrl-dep-at (σ₁ [ σr ]) (fold-map τ₀ σr σ₁ ⟦ s ⟧tm .idxf .sfunc (gi , i')) w)
                      (fold-map τ₀ σr σ₁ ⟦ s ⟧tm .famf .transf (gi , i') .func (g , e)))) →
               (∀ {i'} (r' : ValRel (σ₂ [ μ τ₀ ]) u i') (o : ∣ 𝔽 (width u) ∣) (e : ∣ Fib (σ₂ [ μ τ₀ ]) i' ∣) →
                  DepRel (σ₂ [ μ τ₀ ]) r' o (Fib._+_ (σ₂ [ μ τ₀ ]) i' (ctrl-dep-at (σ₂ [ μ τ₀ ]) i' w) e) →
                  DepRel (σ₂ [ σr ]) (map-val IHv M₂ rγ r') (ap G (map-input γ w x o))
                    (Fib._+_ (σ₂ [ σr ]) (fold-map τ₀ σr σ₂ ⟦ s ⟧tm .idxf .sfunc (gi , i'))
                      (ctrl-dep-at (σ₂ [ σr ]) (fold-map τ₀ σr σ₂ ⟦ s ⟧tm .idxf .sfunc (gi , i')) w)
                      (fold-map τ₀ σr σ₂ ⟦ s ⟧tm .famf .transf (gi , i') .func (g , e)))) →
               (o : ∣ 𝔽 (suc (width v + width u)) ∣) (e : ∣ Fib ((σ₁ [×] σ₂) [ μ τ₀ ]) i ∣) →
               DepRel ((σ₁ [×] σ₂) [ μ τ₀ ]) {pair v u} {i} r o
                 (Fib._+_ ((σ₁ [×] σ₂) [ μ τ₀ ]) i (ctrl-dep-at ((σ₁ [×] σ₂) [ μ τ₀ ]) i w) e) →
               DepRel ((σ₁ [×] σ₂) [ σr ]) {pair v' u'} {fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)}
                 (map-val {s = s} IHv {σ₁ [×] σ₂} (m-pair M₁ M₂) rγ {i} r)
                 (ap (map-built-out γ (width v + width u) (width v' + width u') M.+ₘ
                      (M.in₂ {1} ∘ ⟨ F ∘ sub-inputs γ (M.p₁ {width v} {width u} ∘ M.p₂ {1} {width v + width u}) ,
                                     G ∘ sub-inputs γ (M.p₂ {width v} {width u} ∘ M.p₂ {1} {width v + width u}) ⟩))
                     (map-input γ w x o))
                 (Fib._+_ ((σ₁ [×] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i))
                   (ctrl-dep-at ((σ₁ [×] σ₂) [ σr ]) (fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm .idxf .sfunc (gi , i)) w)
                   (fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)))
map-dep-pair {γ = γ} {τ₀} {σr} {s} IHv {σ₁} {σ₂} {v} {v'} {u} {u'} {F} {G} M₁ M₂ {gi} rγ {i} (r₁ , r₂) w x g IHM₁ IHM₂ o e
             (h₀ , (h₁ , h₂)) =
  root-eq ,
  (DepRel-at-bound (σ₁ [ σr ]) (ValRel-resp (σ₁ [ σr ]) (proj₁ E⁻) rv₁)
     (DepRel-transport⁻ (σ₁ [ σr ]) (proj₁ E) rv₁ ed₁
        (DepRel-resp (σ₁ [ σr ]) rv₁ (λ k → ≈-sym (comp₁ k)) (Fib.refl (σ₁ [ σr ]) I₁) (IHM₁ r₁' o₁ e₁ h₁'))) ,
   DepRel-at-bound (σ₂ [ σr ]) (ValRel-resp (σ₂ [ σr ]) (proj₂ E⁻) rv₂)
     (DepRel-transport⁻ (σ₂ [ σr ]) (proj₂ E) rv₂ ed₂
        (DepRel-resp (σ₂ [ σr ]) rv₂ (λ k → ≈-sym (comp₂ k)) (Fib.refl (σ₂ [ σr ]) I₂) (IHM₂ r₂' o₂ e₂ h₂'))))
  where
  open PairShape τ₀ σr s σ₁ σ₂
  open Idx gi i
  r₁' = ValRel-at-bound (σ₁ [ μ τ₀ ]) r₁
  r₂' = ValRel-at-bound (σ₂ [ μ τ₀ ]) r₂
  rv₁ = map-val IHv M₁ rγ r₁'
  rv₂ = map-val IHv M₂ rγ r₂'
  E⁻ = Ix.sym τ× {I×} {I₁ , I₂} E
  e₁ = proj₁ (proj₂ e)
  e₂ = proj₂ (proj₂ e)
  y = map-input γ w x o
  o₁ = ap (M.p₁ {width v} {width u}) (λ k → o (suc k))
  o₂ = ap (M.p₂ {width v} {width u}) (λ k → o (suc k))
  C₁ = M.p₁ {width v} {width u} ∘ M.p₂ {1} {width v + width u}
  C₂ = M.p₂ {width v} {width u} ∘ M.p₂ {1} {width v + width u}
  Q = ⟨ F ∘ sub-inputs γ C₁ , G ∘ sub-inputs γ C₂ ⟩
  F' = map-built-out γ (width v + width u) (width v' + width u') M.+ₘ (M.in₂ {1} ∘ Q)
  dF = F× .famf .transf (gi , i) .func (g , e)
  D = Fib._+_ τ× I× (ctrl-dep-at τ× I× w) dF
  fib = pair-fibre {τ₀ = τ₀} s σ₁ σ₂ gi i g e
  cdμ = ctrl-dep-pair {σ₁ [ μ τ₀ ]} {σ₂ [ μ τ₀ ]} i₁ i₂ w
  cd× = ctrl-dep-pair {σ₁ [ σr ]} {σ₂ [ σr ]} (proj₁ I×) (proj₂ I×) w
  h₁' : DepRel (σ₁ [ μ τ₀ ]) r₁' o₁ (Fib._+_ (σ₁ [ μ τ₀ ]) i₁ (ctrl-dep-at (σ₁ [ μ τ₀ ]) i₁ w) e₁)
  h₁' = DepRel-resp (σ₁ [ μ τ₀ ]) r₁' (λ k → ≈-refl)
          (Fib.+-cong (σ₁ [ μ τ₀ ]) i₁ (proj₁ (proj₂ cdμ)) (Fib.refl (σ₁ [ μ τ₀ ]) i₁))
          (DepRel-at-bound (σ₁ [ μ τ₀ ]) r₁ h₁)
  h₂' : DepRel (σ₂ [ μ τ₀ ]) r₂' o₂ (Fib._+_ (σ₂ [ μ τ₀ ]) i₂ (ctrl-dep-at (σ₂ [ μ τ₀ ]) i₂ w) e₂)
  h₂' = DepRel-resp (σ₂ [ μ τ₀ ]) r₂' (λ k → ≈-refl)
          (Fib.+-cong (σ₂ [ μ τ₀ ]) i₂ (proj₂ (proj₂ cdμ)) (Fib.refl (σ₂ [ μ τ₀ ]) i₂))
          (DepRel-at-bound (σ₂ [ μ τ₀ ]) r₂ h₂)
  root-fib : proj₁ dF ≈s proj₁ e
  root-fib = ≈-trans (≈-sym +-runit) (proj₁ fib)
  pay₁ : Fib._≈_ (σ₁ [ σr ]) I₁ (⟦ σ₁ [ σr ] ⟧ .fam .subst {proj₁ I×} {I₁} (proj₁ E) .func (proj₁ (proj₂ dF)))
                                (F₁ .famf .transf (gi , i₁) .func (g , e₁))
  pay₁ = Fib.trans (σ₁ [ σr ]) I₁ (Fib.sym (σ₁ [ σr ]) I₁ (Fib.trans (σ₁ [ σr ]) I₁ (Fib.+-lunit (σ₁ [ σr ]) I₁) (Fib.+-runit (σ₁ [ σr ]) I₁)))
           (proj₁ (proj₂ fib))
  pay₂ : Fib._≈_ (σ₂ [ σr ]) I₂ (⟦ σ₂ [ σr ] ⟧ .fam .subst {proj₂ I×} {I₂} (proj₂ E) .func (proj₂ (proj₂ dF)))
                                (F₂ .famf .transf (gi , i₂) .func (g , e₂))
  pay₂ = Fib.trans (σ₂ [ σr ]) I₂ (Fib.sym (σ₂ [ σr ]) I₂ (Fib.trans (σ₂ [ σr ]) I₂ (Fib.+-lunit (σ₂ [ σr ]) I₂) (Fib.+-lunit (σ₂ [ σr ]) I₂)))
           (proj₂ (proj₂ fib))
  root-eq : ap F' y zero ≈s proj₁ D
  root-eq =
    ≈-trans (map-built γ Q w x o zero)
    (≈-trans (+-cong ≈-refl (≈-trans h₀ (+-cong (proj₁ cdμ) ≈-refl)))
    (≈-trans (≈-sym +-assoc)
    (≈-trans (+-cong (+-idem (ctrl ·ₛ w)) ≈-refl)
    (≈-sym (+-cong (proj₁ cd×) root-fib)))))
  ed₁ : Fib._≈_ (σ₁ [ σr ]) I₁ (⟦ σ₁ [ σr ] ⟧ .fam .subst {proj₁ I×} {I₁} (proj₁ E) .func (proj₁ (proj₂ D)))
                               (Fib._+_ (σ₁ [ σr ]) I₁ (ctrl-dep-at (σ₁ [ σr ]) I₁ w) (F₁ .famf .transf (gi , i₁) .func (g , e₁)))
  ed₁ = Fib.trans (σ₁ [ σr ]) I₁ (⟦ σ₁ [ σr ] ⟧ .fam .subst {proj₁ I×} {I₁} (proj₁ E) .preserve-+ {proj₁ (proj₂ (ctrl-dep-at τ× I× w))} {proj₁ (proj₂ dF)})
          (Fib.+-cong (σ₁ [ σr ]) I₁
             (Fib.trans (σ₁ [ σr ]) I₁ (⟦ σ₁ [ σr ] ⟧ .fam .subst {proj₁ I×} {I₁} (proj₁ E) .func-resp-≈ (proj₁ (proj₂ cd×)))
                                       (ctrl-dep-natural (σ₁ [ σr ]) {proj₁ I×} {I₁} (proj₁ E) w))
             pay₁)
  ed₂ : Fib._≈_ (σ₂ [ σr ]) I₂ (⟦ σ₂ [ σr ] ⟧ .fam .subst {proj₂ I×} {I₂} (proj₂ E) .func (proj₂ (proj₂ D)))
                               (Fib._+_ (σ₂ [ σr ]) I₂ (ctrl-dep-at (σ₂ [ σr ]) I₂ w) (F₂ .famf .transf (gi , i₂) .func (g , e₂)))
  ed₂ = Fib.trans (σ₂ [ σr ]) I₂ (⟦ σ₂ [ σr ] ⟧ .fam .subst {proj₂ I×} {I₂} (proj₂ E) .preserve-+ {proj₂ (proj₂ (ctrl-dep-at τ× I× w))} {proj₂ (proj₂ dF)})
          (Fib.+-cong (σ₂ [ σr ]) I₂
             (Fib.trans (σ₂ [ σr ]) I₂ (⟦ σ₂ [ σr ] ⟧ .fam .subst {proj₂ I×} {I₂} (proj₂ E) .func-resp-≈ (proj₂ (proj₂ cd×)))
                                       (ctrl-dep-natural (σ₂ [ σr ]) {proj₂ I×} {I₂} (proj₂ E) w))
             pay₂)
  tail : ∀ k → ap F' y (suc k) ≈s M.concat (ap (F ∘ sub-inputs γ C₁) y) (ap (G ∘ sub-inputs γ C₂) y) k
  tail k = ≈-trans (map-built γ Q w x o (suc k)) (app-pair (F ∘ sub-inputs γ C₁) (G ∘ sub-inputs γ C₂) y k)
  sub₁ : ∀ l → map-input γ w x (ap C₁ o) l ≈s map-input γ w x o₁ l
  sub₁ l = +-cong ≈-refl (app-congᵥ (M.in₂ {suc (width-env γ)} {width v})
             (λ m → ≈-trans (app-∘ (M.p₁ {width v} {width u}) (M.p₂ {1} {width v + width u}) o m)
                            (app-congᵥ (M.p₁ {width v} {width u}) (ap-p₂₁ o) m)) l)
  sub₂ : ∀ l → map-input γ w x (ap C₂ o) l ≈s map-input γ w x o₂ l
  sub₂ l = +-cong ≈-refl (app-congᵥ (M.in₂ {suc (width-env γ)} {width u})
             (λ m → ≈-trans (app-∘ (M.p₂ {width v} {width u}) (M.p₂ {1} {width v + width u}) o m)
                            (app-congᵥ (M.p₂ {width v} {width u}) (ap-p₂₁ o) m)) l)
  comp₁ : ∀ k → ap (M.p₁ {width v'} {width u'}) (λ l → ap F' y (suc l)) k ≈s ap F (map-input γ w x o₁) k
  comp₁ k =
    ≈-trans (app-congᵥ (M.p₁ {width v'} {width u'}) tail k)
    (≈-trans (app-p₁ {width v'} {width u'} (M.concat (ap (F ∘ sub-inputs γ C₁) y) (ap (G ∘ sub-inputs γ C₂) y)) k)
    (≈-trans (M.split₁-concat (ap (F ∘ sub-inputs γ C₁) y) (ap (G ∘ sub-inputs γ C₂) y) k)
    (≈-trans (app-∘ F (sub-inputs γ C₁) y k)
      (app-congᵥ F (λ l → ≈-trans (ap-sub-inputs γ C₁ w x o l) (sub₁ l)) k))))
  comp₂ : ∀ k → ap (M.p₂ {width v'} {width u'}) (λ l → ap F' y (suc l)) k ≈s ap G (map-input γ w x o₂) k
  comp₂ k =
    ≈-trans (app-congᵥ (M.p₂ {width v'} {width u'}) tail k)
    (≈-trans (app-p₂ {width v'} {width u'} (M.concat (ap (F ∘ sub-inputs γ C₁) y) (ap (G ∘ sub-inputs γ C₂) y)) k)
    (≈-trans (M.split₂-concat (ap (F ∘ sub-inputs γ C₁) y) (ap (G ∘ sub-inputs γ C₂) y) k)
    (≈-trans (app-∘ G (sub-inputs γ C₂) y k)
      (app-congᵥ G (λ l → ≈-trans (ap-sub-inputs γ C₂ w x o l) (sub₂ l)) k))))

private
  mu-fibre : ∀ {Γ} {τ₀ : type 1} {σr : type 0} (s : Γ ▸ τ₀ [ σr ] ⊢ σr) (τ' : type 2) gi
             (i : Ix ((μ τ') [ μ τ₀ ])) (g : ∣ FibC Γ gi ∣) (e : ∣ Fib ((μ τ') [ μ τ₀ ]) i ∣) →
             let τμ = τ' [ μ τ₀ ]₁
                 τₛ = τ' [ σr ]₁
                 Fu = fold-map τ₀ σr (unfold₁ τ') ⟦ s ⟧tm
                 Fμ = fold-map τ₀ σr (μ τ') ⟦ s ⟧tm
                 iu = unroll-mor τμ .idxf .sfunc i
                 i₀ = ty-cast (sym (unfold₁-inst τ' (μ τ₀))) .idxf .sfunc iu
                 Iu = Fu .idxf .sfunc (gi , i₀)
                 Iμ = Fμ .idxf .sfunc (gi , i)
             in
             Fib._≈_ (τₛ [ μ τₛ ]) (unroll-mor τₛ .idxf .sfunc Iμ)
               (⟦ τₛ [ μ τₛ ] ⟧ .fam .subst {ty-cast (unfold₁-inst τ' σr) .idxf .sfunc Iu} {unroll-mor τₛ .idxf .sfunc Iμ}
                  (mu-idx {τ₀ = τ₀} s τ' gi i) .func
                 (ty-cast (unfold₁-inst τ' σr) .famf .transf Iu .func
                   (Fu .famf .transf (gi , i₀) .func
                     (g , ty-cast (sym (unfold₁-inst τ' (μ τ₀))) .famf .transf iu .func (unroll-mor τμ .famf .transf i .func e)))))
               (unroll-mor τₛ .famf .transf Iμ .func (Fμ .famf .transf (gi , i) .func (g , e)))
  mu-fibre {Γ} {τ₀} {σr} s τ' gi i g e =
    Fib.trans T Ju (⟦ T ⟧ .fam .subst {a} {Ju} E .func-resp-≈ (Fib.sym T a Zeq))
    (Fib.trans T Ju (Fib.sym T Ju (subst-trans ⟦ T ⟧ {Jb} {a} {Ju} E-comb E W))
    (Fib.trans T Ju (Fib.sym T Ju (transf-natural {⟦ μ τₛ ⟧} {⟦ T ⟧} (unroll-mor τₛ) {Ib} {Iμ} E-F Xb))
      (unroll-mor τₛ .famf .transf Iμ .func-resp-≈
        (Fib.trans (μ τₛ) Iμ (Fib.sym (μ τₛ) Iμ (transf-natural {Dom} {⟦ μ τₛ ⟧} Fμ {gi , b} {gi , i} Eb Pb))
          (Fμ .famf .transf (gi , i) .func-resp-≈ step₂)))))
    where
    open MuShape τ₀ σr s τ'
    open Idx gi i
    Dom = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ μ τμ ⟧
    Dom₀ = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ (unfold₁ τ') [ μ τ₀ ] ⟧
    Ia = roll-mor τₛ .idxf .sfunc a
    Jb = unroll-mor τₛ .idxf .sfunc Ib
    Ju = unroll-mor τₛ .idxf .sfunc Iμ
    E = mu-idx {τ₀ = τ₀} s τ' gi i
    eu = unroll-mor τμ .famf .transf i .func e
    e₁ = ty-cast (sym eμ) .famf .transf iu .func eu
    P = Fam-P.pair {Dom₀} {⟦ Γ ⟧ctxt} {⟦ μ τμ ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {⟦ (unfold₁ τ') [ μ τ₀ ] ⟧})
          (Fam-cat._∘_ (Fam-cat._∘_ (roll-mor τμ) Cμ) (Fam-P.p₂ {⟦ Γ ⟧ctxt} {⟦ (unfold₁ τ') [ μ τ₀ ] ⟧}))
    Pb = P .famf .transf (gi , i₀) .func (g , e₁)
    Xb = Fμ .famf .transf (gi , b) .func Pb
    W = unroll-mor τₛ .famf .transf Ib .func Xb
    Z = Cₛ .famf .transf Iu .func (Fu .famf .transf (gi , i₀) .func (g , e₁))
    E₀ : Ix._≈_ (μ τₛ) Ib Ia
    E₀ = idx-eq (fold-map-mu τ₀ σr τ' ⟦ s ⟧tm) (gi , i₀)
    E-u : Ix._≈_ T Jb (unroll-mor τₛ .idxf .sfunc Ia)
    E-u = unroll-mor τₛ .idxf .sfunc-resp-≈ {Ib} {Ia} E₀
    E-ur : Ix._≈_ T (unroll-mor τₛ .idxf .sfunc Ia) a
    E-ur = idx-eq (unroll-roll τₛ) a
    E-comb : Ix._≈_ T Jb a
    E-comb = Ix.trans T {Jb} {unroll-mor τₛ .idxf .sfunc Ia} {a} E-u E-ur
    Eb : IxO._≈_ Dom (gi , b) (gi , i)
    Eb = IxC.refl Γ {gi} , e₀
    E-F : Ix._≈_ (μ τₛ) Ib Iμ
    E-F = Fμ .idxf .sfunc-resp-≈ {gi , b} {gi , i} Eb
    Zeq : Fib._≈_ T a (⟦ T ⟧ .fam .subst {Jb} {a} E-comb .func W) Z
    Zeq =
      Fib.trans T a (subst-trans ⟦ T ⟧ {Jb} {unroll-mor τₛ .idxf .sfunc Ia} {a} E-u E-ur W)
      (Fib.trans T a (⟦ T ⟧ .fam .subst {unroll-mor τₛ .idxf .sfunc Ia} {a} E-ur .func-resp-≈
                        (Fib.trans T (unroll-mor τₛ .idxf .sfunc Ia)
                           (Fib.sym T (unroll-mor τₛ .idxf .sfunc Ia) (transf-natural {⟦ μ τₛ ⟧} {⟦ T ⟧} (unroll-mor τₛ) {Ib} {Ia} E₀ Xb))
                           (unroll-mor τₛ .famf .transf Ia .func-resp-≈ (fam-eq (fold-map-mu τ₀ σr τ' ⟦ s ⟧tm) (gi , i₀) (g , e₁)))))
        (fam-eq (unroll-roll τₛ) a Z))
    pay : Fib._≈_ (μ τμ) i
            (⟦ μ τμ ⟧ .fam .subst {b} {i} e₀ .func
              (roll-mor τμ .famf .transf (Cμ .idxf .sfunc i₀) .func (Cμ .famf .transf i₀ .func e₁)))
            e
    pay =
      Fib.trans (μ τμ) i (subst-trans ⟦ μ τμ ⟧ {b} {roll-mor τμ .idxf .sfunc iu} {i} Er (idx-eq (roll-unroll τμ) i)
                            (roll-mor τμ .famf .transf (Cμ .idxf .sfunc i₀) .func (Cμ .famf .transf i₀ .func e₁)))
      (Fib.trans (μ τμ) i (⟦ μ τμ ⟧ .fam .subst {roll-mor τμ .idxf .sfunc iu} {i} (idx-eq (roll-unroll τμ) i) .func-resp-≈
                            (Fib.trans (μ τμ) (roll-mor τμ .idxf .sfunc iu)
                               (Fib.sym (μ τμ) (roll-mor τμ .idxf .sfunc iu)
                                 (transf-natural {⟦ τμ [ μ τμ ] ⟧} {⟦ μ τμ ⟧} (roll-mor τμ) {Cμ .idxf .sfunc i₀} {iu} Ec
                                    (Cμ .famf .transf i₀ .func e₁)))
                               (roll-mor τμ .famf .transf iu .func-resp-≈ (ty-cast-cancel-elt eμ iu eu))))
        (fam-eq (roll-unroll τμ) i e))
    step₂ : FibO._≈_ Dom (gi , i) (Dom .fam .subst {gi , b} {gi , i} Eb .func Pb) (g , e)
    step₂ =
      FibO.trans Dom (gi , i)
        (Dom .fam .subst {gi , b} {gi , i} Eb .func-resp-≈
           (Fpair-elt {Dom₀} {⟦ Γ ⟧ctxt} {⟦ μ τμ ⟧} (Fam-P.p₁ {⟦ Γ ⟧ctxt} {⟦ (unfold₁ τ') [ μ τ₀ ] ⟧})
              (Fam-cat._∘_ (Fam-cat._∘_ (roll-mor τμ) Cμ) (Fam-P.p₂ {⟦ Γ ⟧ctxt} {⟦ (unfold₁ τ') [ μ τ₀ ] ⟧}))
              (gi , i₀) (g , e₁)))
      (FibO.trans Dom (gi , i)
        (Fprod-subst-elt {⟦ Γ ⟧ctxt} {⟦ μ τμ ⟧} {gi} {gi} {b} {i} (IxC.refl Γ {gi}) e₀ g
           (roll-mor τμ .famf .transf (Cμ .idxf .sfunc i₀) .func (Cμ .famf .transf i₀ .func e₁)))
        (subst-refl ⟦ Γ ⟧ctxt {gi} (IxC.refl Γ {gi}) g , pay))

map-dep-mu : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
             (IHv : ∀ {w' u T} (D : γ · w' , s ⇓ u [ T ]) {gj} (rγ : EnvValRel (γ · w') gj) →
                    ValRel σr u (⟦ s ⟧tm .idxf .sfunc gj))
             {τ' : type 2} {v v' F} (M : Map γ s (unfold₁ τ') v v' F) {gi} (rγ : EnvValRel γ gi)
             {i} (r : ValRel ((μ τ') [ μ τ₀ ]) (roll {τ' [ μ τ₀ ]₁} (≡-subst Val (unfold₁-inst τ' (μ τ₀)) v)) i)
             (w : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣) (g : ∣ FibC Γ gi ∣) →
             (∀ {i'} (r' : ValRel ((unfold₁ τ') [ μ τ₀ ]) v i') (o : ∣ 𝔽 (width v) ∣) (e : ∣ Fib ((unfold₁ τ') [ μ τ₀ ]) i' ∣) →
                DepRel ((unfold₁ τ') [ μ τ₀ ]) r' o
                  (Fib._+_ ((unfold₁ τ') [ μ τ₀ ]) i' (ctrl-dep-at ((unfold₁ τ') [ μ τ₀ ]) i' w) e) →
                DepRel ((unfold₁ τ') [ σr ]) (map-val IHv M rγ r') (ap F (map-input γ w x o))
                  (Fib._+_ ((unfold₁ τ') [ σr ]) (fold-map τ₀ σr (unfold₁ τ') ⟦ s ⟧tm .idxf .sfunc (gi , i'))
                    (ctrl-dep-at ((unfold₁ τ') [ σr ]) (fold-map τ₀ σr (unfold₁ τ') ⟦ s ⟧tm .idxf .sfunc (gi , i')) w)
                    (fold-map τ₀ σr (unfold₁ τ') ⟦ s ⟧tm .famf .transf (gi , i') .func (g , e)))) →
             (o : ∣ 𝔽 (width (≡-subst Val (unfold₁-inst τ' (μ τ₀)) v)) ∣) (e : ∣ Fib ((μ τ') [ μ τ₀ ]) i ∣) →
             DepRel ((μ τ') [ μ τ₀ ]) {roll {τ' [ μ τ₀ ]₁} (≡-subst Val (unfold₁-inst τ' (μ τ₀)) v)} {i} r o
               (Fib._+_ ((μ τ') [ μ τ₀ ]) i (ctrl-dep-at ((μ τ') [ μ τ₀ ]) i w) e) →
             DepRel ((μ τ') [ σr ]) {roll {τ' [ σr ]₁} (≡-subst Val (unfold₁-inst τ' σr) v')}
               {fold-map τ₀ σr (μ τ') ⟦ s ⟧tm .idxf .sfunc (gi , i)}
               (map-val {s = s} IHv {μ τ'} (m-mu {τ' = τ'} M) rγ {i} r)
               (ap (rcast (sym (width-subst (unfold₁-inst τ' σr) v')) M.I ∘
                    (F ∘ sub-inputs γ (ccast (sym (width-subst (unfold₁-inst τ' (μ τ₀)) v)) M.I)))
                   (map-input γ w x o))
               (Fib._+_ ((μ τ') [ σr ]) (fold-map τ₀ σr (μ τ') ⟦ s ⟧tm .idxf .sfunc (gi , i))
                 (ctrl-dep-at ((μ τ') [ σr ]) (fold-map τ₀ σr (μ τ') ⟦ s ⟧tm .idxf .sfunc (gi , i)) w)
                 (fold-map τ₀ σr (μ τ') ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)))
map-dep-mu {γ = γ} {τ₀} {σr} {s} IHv {τ'} {v} {v'} {F} M {gi} rγ {i} r w x g IHM o e h =
  DepRel-at-bound T R
    (DepRel-resp T R (λ k → ≈-sym (vec-eq k)) fib-eq
      (DepRel-transport T E (ValRel-cast eₛ rv')
        (DepRel-cast eₛ rv' (IHM r₁ o₁ e₁ h₁))))
  where
  open MuShape τ₀ σr s τ'
  open Idx gi i
  Tu = (unfold₁ τ') [ μ τ₀ ]
  Ts = (unfold₁ τ') [ σr ]
  Ju = unroll-mor τₛ .idxf .sfunc Iμ
  E = mu-idx {τ₀ = τ₀} s τ' gi i
  r₀ = ValRel-at-bound (τμ [ μ τμ ]) r
  r₁ = ValRel-cast⁻ eμ {v = v} r₀
  rv' = map-val IHv M rγ r₁
  R = ValRel-resp T E (ValRel-cast eₛ rv')
  eu = unroll-mor τμ .famf .transf i .func e
  e₁ = ty-cast (sym eμ) .famf .transf iu .func eu
  o₁ = vec-cast⁻ eμ {v} o
  y = map-input γ w x o
  Cc = ccast (sym (width-subst eμ v)) M.I
  dF = Fμ .famf .transf (gi , i) .func (g , e)
  dU = Fu .famf .transf (gi , i₀) .func (g , e₁)
  h₀ : DepRel (τμ [ μ τμ ]) r₀ o (Fib._+_ (τμ [ μ τμ ]) iu (ctrl-dep-at (τμ [ μ τμ ]) iu w) eu)
  h₀ = DepRel-resp (τμ [ μ τμ ]) r₀ (λ k → ≈-refl)
         (Fib.trans (τμ [ μ τμ ]) iu
           (unroll-mor τμ .famf .transf i .preserve-+ {ctrl-dep-at (μ τμ) i w} {e})
           (Fib.+-cong (τμ [ μ τμ ]) iu (preserves-unroll-ctrl-dep τμ .at i .func-eq {w} {w} ≈-refl)
                                        (Fib.refl (τμ [ μ τμ ]) iu)))
         (DepRel-at-bound (τμ [ μ τμ ]) r h)
  h₁ : DepRel Tu r₁ o₁ (Fib._+_ Tu i₀ (ctrl-dep-at Tu i₀ w) e₁)
  h₁ = DepRel-resp Tu r₁ (λ k → ≈-refl)
         (Fib.trans Tu i₀
           (ty-cast (sym eμ) .famf .transf iu .preserve-+ {ctrl-dep-at (τμ [ μ τμ ]) iu w} {eu})
           (Fib.+-cong Tu i₀ (ty-cast-ctrl-dep (sym eμ) iu w) (Fib.refl Tu i₀)))
         (DepRel-cast⁻ eμ {v = v} r₀ h₀)
  vec-eq : ∀ k → ap (rcast (sym (width-subst eₛ v')) M.I ∘ (F ∘ sub-inputs γ Cc)) y k
                 ≈s vec-cast eₛ {v'} (ap F (map-input γ w x o₁)) k
  vec-eq k =
    ≈-trans (app-∘ (rcast (sym (width-subst eₛ v')) M.I) (F ∘ sub-inputs γ Cc) y k)
    (≈-trans (ap-rcast-I eₛ {v'} (ap (F ∘ sub-inputs γ Cc) y) k)
      (vec-cast-cong eₛ {v'}
         (λ l → ≈-trans (app-∘ F (sub-inputs γ Cc) y l)
                        (app-congᵥ F (λ m → ≈-trans (ap-sub-inputs γ Cc w x o m)
                                                    (+-cong ≈-refl (app-congᵥ (M.in₂ {suc (width-env γ)} {width v}) (ap-ccast-I eμ {v} o) m))) l))
         k))
  fib-eq : Fib._≈_ T Ju
             (⟦ T ⟧ .fam .subst {a} {Ju} E .func (Cₛ .famf .transf Iu .func (Fib._+_ Ts Iu (ctrl-dep-at Ts Iu w) dU)))
             (unroll-mor τₛ .famf .transf Iμ .func (Fib._+_ (μ τₛ) Iμ (ctrl-dep-at (μ τₛ) Iμ w) dF))
  fib-eq =
    Fib.trans T Ju (⟦ T ⟧ .fam .subst {a} {Ju} E .func-resp-≈
                      (Fib.trans T a (Cₛ .famf .transf Iu .preserve-+ {ctrl-dep-at Ts Iu w} {dU})
                                     (Fib.+-cong T a (ty-cast-ctrl-dep eₛ Iu w) (Fib.refl T a))))
    (Fib.trans T Ju (subst-ctrl-dep+ T {a} {Ju} E w (Cₛ .famf .transf Iu .func dU))
    (Fib.trans T Ju (Fib.+-cong T Ju (Fib.refl T Ju) (mu-fibre {τ₀ = τ₀} s τ' gi i g e))
    (Fib.sym T Ju
      (Fib.trans T Ju (unroll-mor τₛ .famf .transf Iμ .preserve-+ {ctrl-dep-at (μ τₛ) Iμ w} {dF})
                      (Fib.+-cong T Ju (preserves-unroll-ctrl-dep τₛ .at Iμ .func-eq {w} {w} ≈-refl) (Fib.refl T Ju))))))

map-dep : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
          (IHv : ∀ {w' u T} (D : γ · w' , s ⇓ u [ T ]) {gj} (rγ : EnvValRel (γ · w') gj) →
                 ValRel σr u (⟦ s ⟧tm .idxf .sfunc gj))
          (IHd : ∀ {w' u T} (D : γ · w' , s ⇓ u [ T ]) {gj} (rγ : EnvValRel (γ · w') gj) (w : Setoid.Carrier A)
                 (x' : ∣ 𝔽 (width-env (γ · w')) ∣) (g' : ∣ FibC (Γ ▸ τ₀ [ σr ]) gj ∣) → EnvDepRel rγ w x' g' →
                 DepRel σr (IHv D rγ) (ap T (inputs (γ · w') w x'))
                   (Fib._+_ σr (⟦ s ⟧tm .idxf .sfunc gj) (ctrl-dep-at σr (⟦ s ⟧tm .idxf .sfunc gj) w)
                     (⟦ s ⟧tm .famf .transf gj .func g')))
          {σ' : type 1} {v v' F} (M : Map γ s σ' v v' F) {gi} (rγ : EnvValRel γ gi) {i} (r : ValRel (σ' [ μ τ₀ ]) v i)
          (w : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣) (g : ∣ FibC Γ gi ∣) → EnvDepRel rγ w x g →
          (o : ∣ 𝔽 (width v) ∣) (e : ∣ Fib (σ' [ μ τ₀ ]) i ∣) →
          DepRel (σ' [ μ τ₀ ]) r o (Fib._+_ (σ' [ μ τ₀ ]) i (ctrl-dep-at (σ' [ μ τ₀ ]) i w) e) →
          DepRel (σ' [ σr ]) (map-val IHv M rγ r) (ap F (map-input γ w x o))
            (Fib._+_ (σ' [ σr ]) (fold-map τ₀ σr σ' ⟦ s ⟧tm .idxf .sfunc (gi , i))
              (ctrl-dep-at (σ' [ σr ]) (fold-map τ₀ σr σ' ⟦ s ⟧tm .idxf .sfunc (gi , i)) w)
              (fold-map τ₀ σr σ' ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)))
map-dep {γ = γ} {τ₀} {σr} {s} IHv IHd (m-rec M D) {gi} rγ {i} r w x g rel o e h =
  map-dep-rec {τ₀ = τ₀} IHv M D rγ {i = i} r w x g rel
    (λ r' o' e' h' → map-dep IHv IHd M rγ r' w x g rel o' e' h')
    (λ rγ' x' g' rel' → IHd D rγ' w x' g' rel') o e h
map-dep {γ = γ} {τ₀} {σr} {s} IHv IHd (m-unit {v = v}) {gi} rγ {i} r w x g rel o e h =
  map-dep-leaf {γ = γ} unit {v = v} r (idx-eq (fold-map-unit τ₀ σr ⟦ s ⟧tm) (gi , i)) w x o
    {e = e} {d = fold-map τ₀ σr unit ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)}
    (fam-eq (fold-map-unit τ₀ σr ⟦ s ⟧tm) (gi , i) (g , e)) h
map-dep {γ = γ} {τ₀} {σr} {s} IHv IHd (m-base {b = b} {v = v}) {gi} rγ {i} r w x g rel o e h =
  map-dep-leaf {γ = γ} (base b) {v = v} r (idx-eq (fold-map-base τ₀ σr b ⟦ s ⟧tm) (gi , i)) w x o
    {e = e} {d = fold-map τ₀ σr (base b) ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)}
    (fam-eq (fold-map-base τ₀ σr b ⟦ s ⟧tm) (gi , i) (g , e)) h
map-dep {γ = γ} {τ₀} {σr} {s} IHv IHd (m-arrow {σ₁ = σ₁} {σ₂ = σ₂} {v = v}) {gi} rγ {i} r w x g rel o e h =
  map-dep-leaf {γ = γ} (σ₁ [→] σ₂) {v = v} r (idx-eq (fold-map-arrow τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i)) w x o
    {e = e} {d = fold-map τ₀ σr (σ₁ [→] σ₂) ⟦ s ⟧tm .famf .transf (gi , i) .func (g , e)}
    (fam-eq (fold-map-arrow τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , i) (g , e)) h
map-dep {γ = γ} {τ₀} {σr} {s} IHv IHd (m-inl {σ₁ = σ₁} {σ₂ = σ₂} M) {gi} rγ {i} r w x g rel o e h =
  map-dep-inl {τ₀ = τ₀} IHv {σ₁ = σ₁} {σ₂ = σ₂} M rγ {i = i} r w x g
    (λ r' o' e' h' → map-dep IHv IHd M rγ r' w x g rel o' e' h') o e h
map-dep {γ = γ} {τ₀} {σr} {s} IHv IHd (m-inr {σ₁ = σ₁} {σ₂ = σ₂} M) {gi} rγ {i} r w x g rel o e h =
  map-dep-inr {τ₀ = τ₀} IHv {σ₁ = σ₁} {σ₂ = σ₂} M rγ {i = i} r w x g
    (λ r' o' e' h' → map-dep IHv IHd M rγ r' w x g rel o' e' h') o e h
map-dep {γ = γ} {τ₀} {σr} {s} IHv IHd (m-pair {σ₁ = σ₁} {σ₂ = σ₂} M₁ M₂) {gi} rγ {i} r w x g rel o e h =
  map-dep-pair {τ₀ = τ₀} IHv {σ₁ = σ₁} {σ₂ = σ₂} M₁ M₂ rγ {i = i} r w x g
    (λ r' o' e' h' → map-dep IHv IHd M₁ rγ r' w x g rel o' e' h')
    (λ r' o' e' h' → map-dep IHv IHd M₂ rγ r' w x g rel o' e' h') o e h
map-dep {γ = γ} {τ₀} {σr} {s} IHv IHd (m-mu {τ' = τ'} M) {gi} rγ {i} r w x g rel o e h =
  map-dep-mu {τ₀ = τ₀} IHv {τ' = τ'} M rγ {i = i} r w x g
    (λ r' o' e' h' → map-dep IHv IHd M rγ r' w x g rel o' e' h') o e h

private
  fold-fibre : ∀ {Γ} {τ₀ : type 1} {σ : type 0} (s : Γ ▸ τ₀ [ σ ] ⊢ σ) (t : Γ ⊢ μ τ₀) gi (g : ∣ FibC Γ gi ∣) →
               let Fv = fold-map τ₀ σ (var zero) ⟦ s ⟧tm
                   it = ⟦ t ⟧tm .idxf .sfunc gi
               in
               Fib._≈_ σ (⟦ fold s t ⟧tm .idxf .sfunc gi)
                 (⟦ σ ⟧ .fam .subst (idx-eq (fold-map-var τ₀ σ ⟦ s ⟧tm) (gi , it)) .func
                   (Fv .famf .transf (gi , it) .func (g , ⟦ t ⟧tm .famf .transf gi .func g)))
                 (⟦ fold s t ⟧tm .famf .transf gi .func g)
  fold-fibre {Γ} {τ₀} {σ} s t gi g =
    Fib.trans σ J
      (⟦ σ ⟧ .fam .subst {IF} {J} E .func-resp-≈
        (Fv .famf .transf (gi , it) .func-resp-≈
          (FibO.sym Dom (gi , it)
            (Fpair-elt {⟦ Γ ⟧ctxt} {⟦ Γ ⟧ctxt} {⟦ μ τ₀ ⟧} (Fam-cat.id ⟦ Γ ⟧ctxt) ⟦ t ⟧tm gi g))))
      (fam-eq (fold-map-var τ₀ σ ⟦ s ⟧tm) (gi , it) Pg)
    where
    Fv = fold-map τ₀ σ (var zero) ⟦ s ⟧tm
    it = ⟦ t ⟧tm .idxf .sfunc gi
    IF = Fv .idxf .sfunc (gi , it)
    J = ⟦ fold s t ⟧tm .idxf .sfunc gi
    E = idx-eq (fold-map-var τ₀ σ ⟦ s ⟧tm) (gi , it)
    Dom = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ μ τ₀ ⟧
    Pg = Fam-P.pair (Fam-cat.id ⟦ Γ ⟧ctxt) ⟦ t ⟧tm .famf .transf gi .func g

fundamental-val : ∀ {Γ τ} {t : Γ ⊢ τ} {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ])
       {gi} (rγ : EnvValRel γ gi) → ValRel τ v (⟦ t ⟧tm .idxf .sfunc gi)
fundamental-vals : ∀ {Γ is} {Ms : Every (λ σ → Γ ⊢ base σ) is} {γ : Env Γ} {vs R}
        (D : γ , Ms ⇓s vs [ R ]) {gi} (rγ : EnvValRel γ gi) →
        Prf (Setoid._≈_ (sort-vals-setoid sort-index is) (args-idx Ms gi) vs)
fundamental-val (⇓-var x) rγ = lookup-val x rγ
fundamental-val ⇓-unit rγ = tt
fundamental-val {τ = τ₁ [+] τ₂} (⇓-inl {t = t} D) {gi} rγ =
  ⟦ t ⟧tm .idxf .sfunc gi , ValRel-at-bound τ₁ (fundamental-val D rγ) ,
  ⟪ Ix.refl (τ₁ [+] τ₂) {inj₁ (⟦ t ⟧tm .idxf .sfunc gi)} ⟫
fundamental-val {τ = τ₁ [+] τ₂} (⇓-inr {t = t} D) {gi} rγ =
  ⟦ t ⟧tm .idxf .sfunc gi , ValRel-at-bound τ₂ (fundamental-val D rγ) ,
  ⟪ Ix.refl (τ₁ [+] τ₂) {inj₂ (⟦ t ⟧tm .idxf .sfunc gi)} ⟫
fundamental-val {Γ = Γ} {τ = τ} (⇓-case-l {τ₁ = τ₁} {τ₂ = τ₂} {s = s} {t₁ = t₁} {t₂ = t₂} D₁ D₂) {gi} rγ =
  let (i' , r , ⟪ e ⟫) = fundamental-val D₁ rγ in
  ValRel-resp τ (Ix.sym τ (case-idx s t₁ t₂ gi (inj₁ i') e))
    (fundamental-val D₂ (rγ · ValRel-at-bound τ₁ r))
fundamental-val {Γ = Γ} {τ = τ} (⇓-case-r {τ₁ = τ₁} {τ₂ = τ₂} {s = s} {t₁ = t₁} {t₂ = t₂} D₁ D₂) {gi} rγ =
  let (i' , r , ⟪ e ⟫) = fundamental-val D₁ rγ in
  ValRel-resp τ (Ix.sym τ (case-idx s t₁ t₂ gi (inj₂ i') e))
    (fundamental-val D₂ (rγ · ValRel-at-bound τ₂ r))
fundamental-val {τ = τ₁ [×] τ₂} (⇓-pair D₁ D₂) rγ =
  ValRel-at-bound τ₁ (fundamental-val D₁ rγ) , ValRel-at-bound τ₂ (fundamental-val D₂ rγ)
fundamental-val {τ = τ₁} (⇓-fst {τ₂ = τ₂} D) rγ = ValRel-at-bound τ₁ (proj₁ (fundamental-val D rγ))
fundamental-val {τ = τ₂} (⇓-snd {τ₁ = τ₁} D) rγ = ValRel-at-bound τ₂ (proj₂ (fundamental-val D rγ))
fundamental-val (⇓-lam {σ = σ} {τ = τ}) rγ {v} {j} rv {u} {U} D =
  ValRel-at-bound τ (fundamental-val D (rγ · ValRel-at-bound σ rv))
fundamental-val (⇓-app {σ = σ} {τ = τ} D₁ D₂ D₃) rγ =
  ValRel-at-bound τ
    (fundamental-val D₁ rγ (ValRel-at-bound σ (fundamental-val D₂ rγ)) D₃)
fundamental-val {τ = μ τ} (⇓-roll {t = t} D) {gi} rγ =
  ValRel-at-bound (τ [ μ τ ]) (ValRel-resp (τ [ μ τ ]) e (fundamental-val D rγ))
  where
  i  = ⟦ t ⟧tm .idxf .sfunc gi
  i₂ = unroll-mor τ .idxf .sfunc (roll-mor τ .idxf .sfunc i)
  e : Ix._≈_ (τ [ μ τ ]) i i₂
  e = Ix.sym (τ [ μ τ ]) {i₂} {i}
        (idx-eq (unroll-roll τ) i)
fundamental-val (⇓-fold {τ = τ₀} {σ = σ} {s = s} {t = t} D M) {gi} rγ =
  ValRel-resp σ (idx-eq (fold-map-var τ₀ σ ⟦ s ⟧tm) (gi , ⟦ t ⟧tm .idxf .sfunc gi))
    (map-val {s = s} (λ D' rγ' → fundamental-val D' rγ') M rγ {i = ⟦ t ⟧tm .idxf .sfunc gi}
      (fundamental-val D rγ))
fundamental-val (⇓-bop {ω = ω} D) rγ = ⟪ op-fun ω .sfunc-resp-≈ (Prf.prf (fundamental-vals D rγ)) ⟫
fundamental-val (⇓-brel {ω = ω} {Ms = Ms} {vs = vs} D) {gi} rγ =
  ValRel-bool (rel-pred ω .sfunc vs) (⟦ brel ω Ms ⟧tm .idxf .sfunc gi)
    ⟪ brel-idx ω Ms gi vs (Prf.prf (fundamental-vals D rγ)) ⟫

fundamental-vals [] rγ = ⟪ prop.tt ⟫
fundamental-vals (D ∷ Ds) rγ = ⟪ Prf.prf (fundamental-val D rγ) , Prf.prf (fundamental-vals Ds rγ) ⟫
app-case : ∀ {Γ τ'} {γ : Env Γ} (v : Val τ') {n} (R_s : M.Matrix (suc (width v)) (suc (width-env γ)))
           (T : M.Matrix n (suc (width-env (γ · v)))) s x (k : Fin n) →
           ap (T ∘ (branch-inputs γ v ∘ ⟨ M.I , R_s ⟩)) (inputs γ s x) k
           ≈s ap T (inputs (γ · v) (ap R_s (inputs γ s x) zero +ₛ (ctrl ·ₛ s))
                     (λ l → ap (M.in₁ {width-env γ} {width v}) x l +ₛ
                            ap (M.in₂ {width-env γ} {width v}) (λ m → ap R_s (inputs γ s x) (suc m)) l)) k
app-case {γ = γ} v R_s T s x k =
  ≈-trans (app-∘ T (branch-inputs γ v ∘ ⟨ M.I , R_s ⟩) (inputs γ s x) k) (app-congᵥ T (ap-branch-inputs γ v R_s s x) k)

private
  proj-op : ∀ {Γ τ'} {γ : Env Γ} (wv : Val τ') {m n} (P : M.Matrix (width wv) (m + n))
            (R' : M.Matrix (suc (m + n)) (suc (width-env γ))) s x k →
            ap (elim-out γ wv +ₘ (proj-up {m} {n} wv P ∘ R')) (inputs γ s x) k
            ≈s (ap (ctrl-of wv) (λ _ → (ctrl ·ₛ s) +ₛ ap R' (inputs γ s x) zero) k +ₛ
                ap P (λ l → ap R' (inputs γ s x) (suc l)) k)
  proj-op {γ = γ} wv {m} {n} P R' s x k =
    ≈-trans (app-+ₘ (elim-out γ wv) (proj-up {m} {n} wv P ∘ R') (inputs γ s x) k)
    (≈-trans (+-cong (≈-trans (app-∘ (ctrl-of wv) wctrl (inputs γ s x) k)
                              (app-congᵥ (ctrl-of wv) (λ l → ap-wctrl {width-env γ} {1} (inputs γ s x) l) k))
                     (≈-trans (app-∘ (proj-up {m} {n} wv P) R' (inputs γ s x) k)
                     (≈-trans (app-+ₘ (P ∘ M.p₂ {1} {m + n}) (ctrl-of wv ∘ M.p₁ {1} {m + n}) o' k)
                              (+-cong (≈-trans (app-∘ P (M.p₂ {1} {m + n}) o' k)
                                               (app-congᵥ P (ap-p₂₁ {m + n} o') k))
                                      (≈-trans (app-∘ (ctrl-of wv) (M.p₁ {1} {m + n}) o' k)
                                               (app-congᵥ (ctrl-of wv) (ap-p₁₁ {m + n} o') k))))))
    (≈-trans (+-cong ≈-refl +-comm)
    (≈-trans (≈-sym +-assoc)
             (+-cong (≈-sym (app-+ (ctrl-of wv) (λ _ → ctrl ·ₛ s) (λ _ → o' zero) k)) ≈-refl))))
    where o' = ap R' (inputs γ s x)

private
  proj-den : ∀ τ' (i : Ix τ') s a₀ o'₀ (comp G m : ∣ Fib τ' i ∣) →
             o'₀ ≈s ((ctrl ·ₛ s) +ₛ a₀) →
             Fib._≈_ τ' i comp (Fib._+_ τ' i (ctrl-dep-at τ' i s) m) →
             Fib._≈_ τ' i G (Fib._+_ τ' i m (ctrl-dep-at τ' i a₀)) →
             Fib._≈_ τ' i (Fib._+_ τ' i (ctrl-dep-at τ' i ((ctrl ·ₛ s) +ₛ o'₀)) comp) (Fib._+_ τ' i (ctrl-dep-at τ' i s) G)
  proj-den τ' i s a₀ o'₀ comp G m eo ecomp eG =
    Fib.trans τ' i (Fib.+-cong τ' i ctrl-dep-part ecomp)
    (Fib.trans τ' i rearr (Fib.+-cong τ' i (Fib.refl τ' i) (Fib.sym τ' i eG)))
    where
    ctrl-dep-part : Fib._≈_ τ' i (ctrl-dep-at τ' i ((ctrl ·ₛ s) +ₛ o'₀)) (Fib._+_ τ' i (ctrl-dep-at τ' i s) (ctrl-dep-at τ' i a₀))
    ctrl-dep-part = ctrl-dep-split τ' i s a₀ eo
    rearr : Fib._≈_ τ' i (Fib._+_ τ' i (Fib._+_ τ' i (ctrl-dep-at τ' i s) (ctrl-dep-at τ' i a₀)) (Fib._+_ τ' i (ctrl-dep-at τ' i s) m))
                       (Fib._+_ τ' i (ctrl-dep-at τ' i s) (Fib._+_ τ' i m (ctrl-dep-at τ' i a₀)))
    rearr = Fib.trans τ' i (Fib.+-interchange τ' i) (Fib.+-cong τ' i (Fib.⊑-refl τ' i) (Fib.+-comm τ' i))

private
  branch-env : ∀ {Γ τk} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) {v : Val τk} {i'} (r_v : ValRel τk v i')
               s x g (o_s : ∣ 𝔽 (suc (width v)) ∣) (y_v : ∣ Fib τk i' ∣) →
               EnvDepRel rγ s x g → DepRel τk r_v (λ m → o_s (suc m)) (Fib._+_ τk i' y_v (ctrl-dep-at τk i' s)) →
               EnvDepRel (_·_ {τ = τk} {v = v} {i = i'} rγ r_v) (o_s zero +ₛ (ctrl ·ₛ s))
                 (λ m → ap (M.in₁ {width-env γ} {width v}) x m +ₛ ap (M.in₂ {width-env γ} {width v}) (λ m' → o_s (suc m')) m)
                 (g , y_v)
  branch-env {τk = τk} {γ = γ} rγ {v} {i'} r_v s x g o_s y_v rel h =
    EnvDepRel-resp rγ (o_s zero +ₛ (ctrl ·ₛ s)) (λ m → ≈-sym (ap-p₁-++ x (λ m' → o_s (suc m')) m)) (EnvDepRel-mono rγ s (o_s zero) rel) ,
    DepRel⊑-resp τk r_v (o_s zero +ₛ (ctrl ·ₛ s)) (λ m → ≈-sym (ap-p₂-++ x (λ m' → o_s (suc m')) m))
      (DepRel⊑-mono τk r_v s (o_s zero) (ctrl-dep-at τk i' s , (Fib.⊑-refl τk i' , h)))

  roundtrip : ∀ τ {i₁ ic : Ix τ} (E : Ix._≈_ τ i₁ ic) (Eidx : Ix._≈_ τ ic i₁)
              (d : ∣ Fib τ ic ∣) →
              Fib._≈_ τ ic (⟦ τ ⟧ .fam .subst E .func (⟦ τ ⟧ .fam .subst Eidx .func d)) d
  roundtrip τ {i₁} {ic} E Eidx d =
    Fib.trans τ ic (Fib.sym τ ic (subst-trans ⟦ τ ⟧ {ic} {i₁} {ic} Eidx E d))
                 (subst-refl ⟦ τ ⟧ {ic} (Ix.trans τ {ic} {i₁} {ic} Eidx E) d)

  case-den : ∀ τ {i₁ ic : Ix τ} (E : Ix._≈_ τ i₁ ic) (Eidx : Ix._≈_ τ ic i₁)
             s a_s o_s₀ (B : ∣ Fib τ i₁ ∣) (CF : ∣ Fib τ ic ∣) →
             o_s₀ ≈s ((ctrl ·ₛ s) +ₛ a_s) →
             Fib._≈_ τ i₁ (⟦ τ ⟧ .fam .subst Eidx .func CF) (Fib._+_ τ i₁ B (ctrl-dep-at τ i₁ a_s)) →
             Fib._≈_ τ ic (⟦ τ ⟧ .fam .subst E .func (Fib._+_ τ i₁ (ctrl-dep-at τ i₁ (o_s₀ +ₛ (ctrl ·ₛ s))) B))
                        (Fib._+_ τ ic (ctrl-dep-at τ ic s) CF)
  case-den τ {i₁} {ic} E Eidx s a_s o_s₀ B CF eo eB =
    Fib.trans τ ic (subst-ctrl-dep+ τ E (o_s₀ +ₛ (ctrl ·ₛ s)) B)
    (Fib.trans τ ic (Fib.+-cong τ ic ctrl-dep-part (Fib.refl τ ic))
    (Fib.trans τ ic (Fib.+-assoc τ ic)
    (Fib.trans τ ic (Fib.+-cong τ ic (Fib.refl τ ic) (Fib.+-comm τ ic))
                  (Fib.+-cong τ ic (Fib.refl τ ic) (Fib.sym τ ic eCF)))))
    where
    ctrl-dep-part : Fib._≈_ τ ic (ctrl-dep-at τ ic (o_s₀ +ₛ (ctrl ·ₛ s))) (Fib._+_ τ ic (ctrl-dep-at τ ic s) (ctrl-dep-at τ ic a_s))
    ctrl-dep-part = Fib.trans τ ic (ctrl-dep τ .at ic .func-resp-≈ +-comm) (ctrl-dep-split τ ic s a_s eo)
    eCF : Fib._≈_ τ ic CF (Fib._+_ τ ic (⟦ τ ⟧ .fam .subst E .func B) (ctrl-dep-at τ ic a_s))
    eCF =
      Fib.trans τ ic (Fib.sym τ ic (roundtrip τ E Eidx CF))
      (Fib.trans τ ic (⟦ τ ⟧ .fam .subst E .func-resp-≈ {⟦ τ ⟧ .fam .subst Eidx .func CF} {Fib._+_ τ i₁ B (ctrl-dep-at τ i₁ a_s)} eB)
      (Fib.trans τ ic (⟦ τ ⟧ .fam .subst E .preserve-+ {B} {ctrl-dep-at τ i₁ a_s})
                    (Fib.+-cong τ ic (Fib.refl τ ic) (ctrl-dep-natural τ E a_s))))

  case-fibre : ∀ {Γ τ₁ τ₂ τ} (sc : Γ ⊢ τ₁ [+] τ₂) (t₁ : Γ ▸ τ₁ ⊢ τ) (t₂ : Γ ▸ τ₂ ⊢ τ) gi (g : ∣ FibC Γ gi ∣)
               (k : Ix (τ₁ [+] τ₂)) (e : Ix._≈_ (τ₁ [+] τ₂) (⟦ sc ⟧tm .idxf .sfunc gi) k) →
               let SC = copair (elimF (ctrl-dep τ) ⟦ t₁ ⟧tm) (elimF (ctrl-dep τ) ⟦ t₂ ⟧tm)
                   sidx = ⟦ sc ⟧tm .idxf .sfunc gi
               in
               Fib._≈_ τ (SC .idxf .sfunc (gi , k))
                 (⟦ τ ⟧ .fam .subst (case-idx sc t₁ t₂ gi k e) .func (⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g))
                 (SC .famf .transf (gi , k) .func (g , ⟦ τ₁ [+] τ₂ ⟧ .fam .subst {sidx} {k} e .func (⟦ sc ⟧tm .famf .transf gi .func g)))
  case-fibre {Γ} {τ₁} {τ₂} {τ} sc t₁ t₂ gi g k e =
    Fib.trans τ (SC .idxf .sfunc (gi , k))
      (Fib.sym τ (SC .idxf .sfunc (gi , k)) (transf-natural SC {gi , sidx} {gi , k} (IxC.refl Γ {gi} , e) Pg))
      (SC .famf .transf (gi , k) .func-resp-≈ Q≈)
    where
    SC = copair (elimF (ctrl-dep τ) ⟦ t₁ ⟧tm) (elimF (ctrl-dep τ) ⟦ t₂ ⟧tm)
    sidx = ⟦ sc ⟧tm .idxf .sfunc gi
    Dom = Fam-P.prod ⟦ Γ ⟧ctxt ⟦ τ₁ [+] τ₂ ⟧
    Pg = Fam-P.pair (Fam-cat.id ⟦ Γ ⟧ctxt) ⟦ sc ⟧tm .famf .transf gi .func g
    Q≈ : FibO._≈_ Dom (gi , k)
           (Dom .fam .subst {gi , sidx} {gi , k} (IxC.refl Γ {gi} , e) .func Pg)
           (g , ⟦ τ₁ [+] τ₂ ⟧ .fam .subst {sidx} {k} e .func (⟦ sc ⟧tm .famf .transf gi .func g))
    Q≈ = FibO.trans Dom (gi , k)
           (Dom .fam .subst {gi , sidx} {gi , k} (IxC.refl Γ {gi} , e) .func-resp-≈
              (Fpair-elt {⟦ Γ ⟧ctxt} {⟦ Γ ⟧ctxt} {⟦ τ₁ [+] τ₂ ⟧} (Fam-cat.id ⟦ Γ ⟧ctxt) ⟦ sc ⟧tm gi g))
           (FibO.trans Dom (gi , k)
              (Fprod-subst-elt {⟦ Γ ⟧ctxt} {⟦ τ₁ [+] τ₂ ⟧} {gi} {gi} {sidx} {k} (IxC.refl Γ {gi}) e g
                 (⟦ sc ⟧tm .famf .transf gi .func g))
              (subst-refl ⟦ Γ ⟧ctxt (IxC.refl Γ {gi}) g , Fib.refl (τ₁ [+] τ₂) k))

args-vec : ∀ {Γ is} (Ms : Every (λ σ → Γ ⊢ base σ) is) (gi : IxC Γ) → ∣ FibC Γ gi ∣ → ∣ 𝔽 (bases-width is) ∣
args-vec {is = is} Ms gi g =
  ap (collect is .Fam⟨𝒞⟩μ.famf .transf (𝒟-arg-product is .idxf .sfunc (⟦ Ms ⟧tms .idxf .sfunc gi)))
     (𝒟-arg-product is .famf .transf (⟦ Ms ⟧tms .idxf .sfunc gi) .func
        (⟦ Ms ⟧tms .famf .transf gi .func g))

private
  args-width : ∀ is → Setoid.Carrier (prim.args is .Fam⟨𝒞⟩μ.idx) → ℕ
  args-width is p = prim.args is .Fam⟨𝒞⟩μ.fam .fm p

  collect-cons : ∀ i is (a : Setoid.Carrier (sort-index i)) (p : Setoid.Carrier (prim.args is .Fam⟨𝒞⟩μ.idx)) →
                 collect (i ∷ is) .Fam⟨𝒞⟩μ.famf .transf (a , p) M.≈ₘ
                 ((M.in₁ {sort-width i} {bases-width is} ∘ M.p₁ {sort-width i} {args-width is p}) +ₘ
                  (M.in₂ {sort-width i} {bases-width is} ∘
                    (collect is .Fam⟨𝒞⟩μ.famf .transf p ∘ M.p₂ {sort-width i} {args-width is p})))
  collect-cons i is a p =
    ≈ₘ-trans (M.id-left {M = M.I ∘ (u₁ +ₘ u₂)})
    (≈ₘ-trans (M.id-left {M = u₁ +ₘ u₂})
      (M.+ₘ-cong (M.∘-cong (≈ₘ-refl {f = M.in₁ {sort-width i} {bases-width is}})
                          (≈ₘ-trans (M.id-left {M = M.I ∘ M.p₁ {sort-width i} {n}}) (M.id-left {M = M.p₁ {sort-width i} {n}})))
                 (M.∘-cong (≈ₘ-refl {f = M.in₂ {sort-width i} {bases-width is}}) (M.id-left {M = C ∘ M.p₂ {sort-width i} {n}}))))
    where
    n = args-width is p
    C = collect is .Fam⟨𝒞⟩μ.famf .transf p
    u₁ = M.in₁ {sort-width i} {bases-width is} ∘ (M.I ∘ (M.I ∘ M.p₁ {sort-width i} {n}))
    u₂ = M.in₂ {sort-width i} {bases-width is} ∘ (M.I ∘ (C ∘ M.p₂ {sort-width i} {n}))

  args-vec-cons : ∀ {Γ i is} (M : Γ ⊢ base i) (Ms : Every (λ σ → Γ ⊢ base σ) is) gi g k →
                  args-vec (M Every.∷ Ms) gi g k ≈s
                  (ap (M.in₁ {sort-width i} {bases-width is}) (⟦ M ⟧tm .famf .transf gi .func g) k +ₛ
                   ap (M.in₂ {sort-width i} {bases-width is}) (args-vec Ms gi g) k)
  args-vec-cons {i = i} {is} M Ms gi g k =
    ≈-trans (app-congₘ (collect-cons i is a p') Zc k)
    (≈-trans (app-+ₘ (u₁ ∘ M.p₁ {sort-width i} {n}) (u₂ ∘ (C ∘ M.p₂ {sort-width i} {n})) Zc k)
    (+-cong (≈-trans (app-∘ u₁ (M.p₁ {sort-width i} {n}) Zc k)
                     (app-congᵥ u₁ (λ l → ≈-trans (app-congᵥ (M.p₁ {sort-width i} {n}) Zc-split l)
                                                    (ap-p₁-++ y₁ tp-ys l)) k))
            (≈-trans (app-∘ u₂ (C ∘ M.p₂ {sort-width i} {n}) Zc k)
                     (app-congᵥ u₂ (λ l → ≈-trans (app-∘ C (M.p₂ {sort-width i} {n}) Zc l)
                                                    (app-congᵥ C (λ l' → ≈-trans (app-congᵥ (M.p₂ {sort-width i} {n}) Zc-split l')
                                                                                   (ap-p₂-++ y₁ tp-ys l')) l)) k))))
    where
    a = ⟦ M ⟧tm .idxf .sfunc gi
    p = ⟦ Ms ⟧tms .idxf .sfunc gi
    p' = 𝒟-arg-product is .idxf .sfunc p
    n = args-width is p'
    u₁ = M.in₁ {sort-width i} {bases-width is}
    u₂ = M.in₂ {sort-width i} {bases-width is}
    C = collect is .Fam⟨𝒞⟩μ.famf .transf p'
    y₁ = ⟦ M ⟧tm .famf .transf gi .func g
    ys = ⟦ Ms ⟧tms .famf .transf gi .func g
    q = ⟦ M Every.∷ Ms ⟧tms .famf .transf gi .func g
    tp-ys = 𝒟-arg-product is .famf .transf p .func ys
    Zc = 𝒟-arg-product (i ∷ is) .famf .transf (a , p) .func q
    z = Fam-P.prod-m (Fam-cat.id ⟦ base i ⟧) (𝒟-arg-product is) .famf .transf (a , p) .func q

    q≈ = Fpair-elt ⟦ M ⟧tm ⟦ Ms ⟧tms gi g
    ArgsD = signature.PointedFPCat.list→product
              signature.PFPC[ Fam⟨𝒟⟩μ.cat , Fam⟨𝒟⟩μ.terminal SemiMod.terminal , Fam⟨𝒟⟩μ.products , interp.𝒟Bool ]
              (signature.Model.⟦sort⟧ interp.𝒟-Sig-model) is .fam .fm p
    Q = SemiMod._⊕_ (𝔽 (sort-width i)) ArgsD
    f₁ = SemiMod._∘_ (SemiMod.id (𝔽 (sort-width i))) (SemiMod.p₁ {𝔽 (sort-width i)} {ArgsD})
    f₂ = SemiMod._∘_ (𝒟-arg-product is .famf .transf p) (SemiMod.p₂ {𝔽 (sort-width i)} {ArgsD})

    z≈ : (∀ l → proj₁ z l ≈s y₁ l) ∧ (∀ l → proj₂ z l ≈s tp-ys l)
    z≈ = (λ l → ≈-trans (proj₁ (bpair-elt {Q} {𝔽 (sort-width i)} {𝔽 n} f₁ f₂ q) l) (proj₁ q≈ l)) ,
         (λ l → ≈-trans (proj₂ (bpair-elt {Q} {𝔽 (sort-width i)} {𝔽 n} f₁ f₂ q) l)
                        (𝒟-arg-product is .famf .transf p .func-resp-≈ (proj₂ q≈) l))

    Zc-split : ∀ l → Zc l ≈s (ap (M.in₁ {sort-width i} {n}) y₁ l +ₛ ap (M.in₂ {sort-width i} {n}) tp-ys l)
    Zc-split l = +-cong (app-congᵥ (M.in₁ {sort-width i} {n}) (proj₁ z≈) l)
                        (app-congᵥ (M.in₂ {sort-width i} {n}) (proj₂ z≈) l)

  ap-p₁-const : ∀ {m n} (a : Setoid.Carrier A) (l : Fin m) → ap (M.p₁ {m} {n}) (λ _ → a) l ≈s a
  ap-p₁-const {suc m} {n} a zero =
    ≈-trans (+-cong ·-lunit (≈-trans (Σ-cong {m + n} (λ _ → ε-annihilₗ)) (Σ-ε {m + n}))) +-runit
  ap-p₁-const {suc m} a (suc l) = ≈-trans (+-cong ε-annihilₗ (ap-p₁-const {m} a l)) +-lunit

  ap-p₂-const : ∀ {m n} (a : Setoid.Carrier A) (l : Fin n) → ap (M.p₂ {m} {n}) (λ _ → a) l ≈s a
  ap-p₂-const {ℕ.zero} {n} a l = Σ-unit {n} l (λ _ → a)
  ap-p₂-const {suc m} a l = ≈-trans (+-cong ε-annihilₗ (ap-p₂-const {m} a l)) +-lunit

  in-const : ∀ {m n} (a : Setoid.Carrier A) (k : Fin (m + n)) →
             (ap (M.in₁ {m} {n}) (λ _ → a) k +ₛ ap (M.in₂ {m} {n}) (λ _ → a) k) ≈s a
  in-const {m} {n} a k =
    ≈-trans (+-cong (app-congᵥ (M.in₁ {m} {n}) (λ l → ≈-sym (ap-p₁-const {m} {n} a l)) k)
                    (app-congᵥ (M.in₂ {m} {n}) (λ l → ≈-sym (ap-p₂-const {m} {n} a l)) k))
    (≈-trans (+-cong (≈-sym (app-∘ (M.in₁ {m} {n}) (M.p₁ {m} {n}) (λ _ → a) k))
                     (≈-sym (app-∘ (M.in₂ {m} {n}) (M.p₂ {m} {n}) (λ _ → a) k)))
    (≈-trans (≈-sym (app-+ₘ (M.in₁ {m} {n} ∘ M.p₁ {m} {n}) (M.in₂ {m} {n} ∘ M.p₂ {m} {n}) (λ _ → a) k))
    (≈-trans (app-congₘ (M.id-+ m n) (λ _ → a) k) (app-I (λ _ → a) k))))

private
  test-branch : ∀ {n} (D : M.Matrix 1 n) (o : ∣ 𝔽 2 ∣) (a : Setoid.Carrier A) (v : ∣ 𝔽 1 ∣) s
                (y : ∣ 𝔽 n ∣) →
                (∀ k → o k ≈s ((ctrl ·ₛ s) +ₛ ap (⟨ D , εₘ ⟩) (λ l → (ctrl ·ₛ s) +ₛ y l) k)) →
                a ≈s ((ctrl ·ₛ s) +ₛ ap D y zero) → v zero ≈s (ctrl ·ₛ s) →
                (o zero ≈s a) ∧ (∀ k → o (suc k) ≈s v k)
  test-branch {n} D o a v s y ho ha hv = root , payload
    where
    u = λ l → (ctrl ·ₛ s) +ₛ y l
    root : o zero ≈s a
    root =
      ≈-trans (ho zero)
      (≈-trans (+-cong ≈-refl (≈-trans (app-pair {n} {1} {1} D εₘ u zero) (app-+ D (λ _ → ctrl ·ₛ s) y zero)))
      (≈-trans (≈-sym +-assoc)
      (≈-trans (+-cong (≈-trans (+-cong ≈-refl (≈-trans (app-congᵥ D (λ _ → ≈-sym ·-runit) zero)
                                                          (≈-trans (model.app-· D (ctrl ·ₛ s) (λ _ → ι) zero) (·-cong ·-comm ≈-refl))))
                                (cs-absorb s (ap D (λ _ → ι) zero)))
                       ≈-refl)
               (≈-sym ha))))
    payload : ∀ k → o (suc k) ≈s v k
    payload zero =
      ≈-trans (ho (suc zero))
      (≈-trans (+-cong ≈-refl (≈-trans (app-pair {n} {1} {1} D εₘ u (suc zero)) (app-εₘ {1} u zero)))
               (≈-trans +-runit (≈-sym hv)))

  DepRel-bool : ∀ {is} (ω : rel is) (vs : sort-vals is) b {i : Ix (unit [+] unit)}
                (e : Ix._≈_ (unit [+] unit) i b)
                (o : ∣ 𝔽 (width (bool→val b)) ∣) (d : ∣ Fib (unit [+] unit) i ∣) s
                (y : ∣ 𝔽 (bases-width is) ∣) →
                (∀ k → o k ≈s ((ctrl ·ₛ s) +ₛ ap (brel-deps ω vs b) (λ l → (ctrl ·ₛ s) +ₛ y l) k)) →
                Fib._≈_ (unit [+] unit) b (⟦ unit [+] unit ⟧ .fam .subst {i} {b} e .func d)
                (Fib._+_ (unit [+] unit) b (ctrl-dep-at (unit [+] unit) b s)
                   (interp.bool-elt b (ap (rel-deps ω .sfunc vs) y zero))) →
                DepRel (unit [+] unit) {bool→val b} {i} (ValRel-bool b i ⟪ e ⟫) o d
  DepRel-bool ω vs (inj₁ x) {i} e o d s y ho (hd₁ , hd₂) =
    test-branch (rel-deps ω .sfunc vs) o (proj₁ d') (proj₂ d') s y ho
      (≈-trans hd₁ (+-cong (proj₁ (ctrl-dep-inj₁ {unit} {unit} x s)) ≈-refl))
      (≈-trans (hd₂ zero) (≈-trans (+-cong (proj₂ (ctrl-dep-inj₁ {unit} {unit} x s) zero) ≈-refl)
                                   (≈-trans +-runit (ctrl-dep-unit x s))))
    where d' = ⟦ unit [+] unit ⟧ .fam .subst {i} {inj₁ x} e .func d
  DepRel-bool ω vs (inj₂ x) {i} e o d s y ho (hd₁ , hd₂) =
    test-branch (rel-deps ω .sfunc vs) o (proj₁ d') (proj₂ d') s y ho
      (≈-trans hd₁ (+-cong (proj₁ (ctrl-dep-inj₂ {unit} {unit} x s)) ≈-refl))
      (≈-trans (hd₂ zero) (≈-trans (+-cong (proj₂ (ctrl-dep-inj₂ {unit} {unit} x s) zero) ≈-refl)
                                   (≈-trans +-runit (ctrl-dep-unit x s))))
    where d' = ⟦ unit [+] unit ⟧ .fam .subst {i} {inj₂ x} e .func d

fundamental : ∀ {Γ τ} {t : Γ ⊢ τ} {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ])
              {gi} (rγ : EnvValRel γ gi) (s : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣)
              (g : ∣ FibC Γ gi ∣) → EnvDepRel rγ s x g →
              DepRel τ (fundamental-val D rγ) (ap R (inputs γ s x))
                (Fib._+_ τ (⟦ t ⟧tm .idxf .sfunc gi)
                  (ctrl-dep τ .at (⟦ t ⟧tm .idxf .sfunc gi) .func s)
                  (⟦ t ⟧tm .famf .transf gi .func g))
fundamental-s : ∀ {Γ is} {Ms : Every (λ σ → Γ ⊢ base σ) is} {γ : Env Γ} {vs R}
                (D : γ , Ms ⇓s vs [ R ]) {gi} (rγ : EnvValRel γ gi) (s : Setoid.Carrier A)
                (x : ∣ 𝔽 (width-env γ) ∣) (g : ∣ FibC Γ gi ∣) → EnvDepRel rγ s x g →
                ∀ k → ap R (inputs γ s x) k ≈s ((ctrl ·ₛ s) +ₛ args-vec Ms gi g k)
fundamental {τ = τ} {γ = γ} (⇓-var x) {gi} rγ s xs g rel =
  DepRel-resp τ (lookup-val x rγ)
    (λ k → ≈-sym (ap-∥ (ctrl-of (lookup x γ)) (proj-var x γ) (inputs γ s xs) k))
    (Fib.refl τ (⟦ x ⟧var .idxf .sfunc gi))
    (DepRel⊑-ctrl τ (lookup-val x rγ) s (lookup-dep x rγ s xs g rel))
fundamental {Γ = Γ} {γ = γ} ⇓-unit {gi} rγ s x g rel = goal
  where
  goal : ∀ k → ap wctrl (inputs γ s x) k ≈s
               (ctrl-dep unit .at (⟦ unit {Γ} ⟧tm .idxf .sfunc gi) .func s k +ₛ
                ⟦ unit {Γ} ⟧tm .famf .transf gi .func g k)
  goal zero =
    ≈-trans (ap-wctrl {width-env γ} {1} (inputs γ s x) zero)
            (≈-sym (≈-trans (+-cong (ctrl-dep-unit (⟦ unit {Γ} ⟧tm .idxf .sfunc gi) s) (≈-refl {ε})) +-runit))
fundamental {Γ = Γ} {τ = τ₁ [+] τ₂} {γ = γ} (⇓-inl {t = t} {v = v} {R = R'} D) {gi} rγ s x g rel =
  ≈-trans (built {γ = γ} R' s x zero)
          (≈-sym (≈-trans (proj₁ (subst-refl ⟦ τ₁ [+] τ₂ ⟧ {inj₁ i'} (Ix.refl (τ₁ [+] τ₂) {inj₁ i'}) d)) root-den)) ,
  DepRel-at-bound τ₁ (fundamental-val D rγ)
    (DepRel-resp τ₁ (fundamental-val D rγ) (λ k → ≈-sym (built {γ = γ} R' s x (suc k)))
      (Fib.sym τ₁ i' (Fib.trans τ₁ i' (proj₂ (subst-refl ⟦ τ₁ [+] τ₂ ⟧ {inj₁ i'} (Ix.refl (τ₁ [+] τ₂) {inj₁ i'}) d))
                                  (Fib.+-cong τ₁ i' (proj₂ (ctrl-dep-inj₁ {τ₁} {τ₂} i' s)) (Fib.refl τ₁ i'))))
      (fundamental D rγ s x g rel))
  where
  i' = ⟦ t ⟧tm .idxf .sfunc gi
  d = Fib._+_ (τ₁ [+] τ₂) (inj₁ i') (ctrl-dep-at (τ₁ [+] τ₂) (inj₁ i') s) (⟦ inl {τ₂ = τ₂} t ⟧tm .famf .transf gi .func g)
  root-den : proj₁ d ≈s (ctrl ·ₛ s)
  root-den = ≈-trans (+-cong (proj₁ (ctrl-dep-inj₁ {τ₁} {τ₂} i' s)) (≈-refl {ε})) +-runit
fundamental {Γ = Γ} {τ = τ₁ [+] τ₂} {γ = γ} (⇓-inr {t = t} {v = v} {R = R'} D) {gi} rγ s x g rel =
  ≈-trans (built {γ = γ} R' s x zero)
          (≈-sym (≈-trans (proj₁ (subst-refl ⟦ τ₁ [+] τ₂ ⟧ {inj₂ i'} (Ix.refl (τ₁ [+] τ₂) {inj₂ i'}) d)) root-den)) ,
  DepRel-at-bound τ₂ (fundamental-val D rγ)
    (DepRel-resp τ₂ (fundamental-val D rγ) (λ k → ≈-sym (built {γ = γ} R' s x (suc k)))
      (Fib.sym τ₂ i' (Fib.trans τ₂ i' (proj₂ (subst-refl ⟦ τ₁ [+] τ₂ ⟧ {inj₂ i'} (Ix.refl (τ₁ [+] τ₂) {inj₂ i'}) d))
                                  (Fib.+-cong τ₂ i' (proj₂ (ctrl-dep-inj₂ {τ₁} {τ₂} i' s)) (Fib.refl τ₂ i'))))
      (fundamental D rγ s x g rel))
  where
  i' = ⟦ t ⟧tm .idxf .sfunc gi
  d = Fib._+_ (τ₁ [+] τ₂) (inj₂ i') (ctrl-dep-at (τ₁ [+] τ₂) (inj₂ i') s) (⟦ inr {τ₁ = τ₁} t ⟧tm .famf .transf gi .func g)
  root-den : proj₁ d ≈s (ctrl ·ₛ s)
  root-den = ≈-trans (+-cong (proj₁ (ctrl-dep-inj₂ {τ₁} {τ₂} i' s)) (≈-refl {ε})) +-runit
fundamental {Γ = Γ} {τ = τ} {γ = γ}
            (⇓-case-l {τ₁ = τ₁} {τ₂ = τ₂} {s = sc} {t₁ = t₁} {t₂ = t₂} {v = v} {u = u} {R = R_s} {T = T} D₁ D₂) {gi} rγ s x g rel =
  DepRel-resp τ (ValRel-resp τ (Ix.sym τ Eidx) (fundamental-val D₂ (rγ · rv'))) (λ k → ≈-sym (app-case {γ = γ} v R_s T s x k))
    (case-den τ (Ix.sym τ Eidx) Eidx s a_s (ap R_s (inputs γ s x) zero) (⟦ t₁ ⟧tm .famf .transf (gi , i') .func (g , y_v))
       (⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g) o_s₀
       (Fib.trans τ (⟦ t₁ ⟧tm .idxf .sfunc (gi , i')) (case-fibre sc t₁ t₂ gi g (inj₁ i') e)
          (elimF-elt {⟦ Γ ⟧ctxt} {⟦ τ₁ ⟧} {⟦ τ ⟧} (ctrl-dep τ) ⟦ t₁ ⟧tm {gi} {i'} g a_s y_v)))
    (DepRel-transport τ (Ix.sym τ Eidx) (fundamental-val D₂ (rγ · rv'))
       (fundamental D₂ (_·_ {τ = τ₁} {v = v} {i = i'} rγ rv') (ap R_s (inputs γ s x) zero +ₛ (ctrl ·ₛ s)) X (g , y_v)
                              (branch-env {τk = τ₁} rγ {v = v} {i' = i'} rv' s x g (ap R_s (inputs γ s x)) y_v rel payload₁)))
  where
  rs = fundamental-val D₁ rγ
  i' = proj₁ rs
  r_v = proj₁ (proj₂ rs)
  rv' = ValRel-at-bound τ₁ r_v
  e : Ix._≈_ (τ₁ [+] τ₂) (⟦ sc ⟧tm .idxf .sfunc gi) (inj₁ i')
  e = prop.Prf.prf (proj₂ (proj₂ rs))
  Eidx : Ix._≈_ τ (⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi) (⟦ t₁ ⟧tm .idxf .sfunc (gi , i'))
  Eidx = case-idx sc t₁ t₂ gi (inj₁ i') e
  X : ∣ 𝔽 (width-env γ + width v) ∣
  X m = ap (M.in₁ {width-env γ} {width v}) x m +ₛ ap (M.in₂ {width-env γ} {width v}) (λ m' → ap R_s (inputs γ s x) (suc m')) m
  SG = ⟦ τ₁ [+] τ₂ ⟧ .fam .subst {⟦ sc ⟧tm .idxf .sfunc gi} {inj₁ i'} e .func (⟦ sc ⟧tm .famf .transf gi .func g)
  a_s = proj₁ SG
  y_v = proj₂ SG
  split-sum = subst-ctrl-dep+ (τ₁ [+] τ₂) {⟦ sc ⟧tm .idxf .sfunc gi} {inj₁ i'} e s (⟦ sc ⟧tm .famf .transf gi .func g)

  o_s₀ : ap R_s (inputs γ s x) zero ≈s ((ctrl ·ₛ s) +ₛ a_s)
  o_s₀ = ≈-trans (proj₁ (fundamental D₁ rγ s x g rel))
                 (≈-trans (proj₁ split-sum) (+-cong (proj₁ (ctrl-dep-inj₁ {τ₁} {τ₂} i' s)) ≈-refl))

  payload₁ : DepRel τ₁ rv' (λ m → ap R_s (inputs γ s x) (suc m)) (Fib._+_ τ₁ i' y_v (ctrl-dep-at τ₁ i' s))
  payload₁ =
    DepRel-resp τ₁ rv' (λ m → ≈-refl)
      (Fib.trans τ₁ i' (proj₂ split-sum)
        (Fib.trans τ₁ i' (Fib.+-cong τ₁ i' (proj₂ (ctrl-dep-inj₁ {τ₁} {τ₂} i' s)) (Fib.refl τ₁ i')) (Fib.+-comm τ₁ i')))
      (DepRel-at-bound τ₁ r_v (proj₂ (fundamental D₁ rγ s x g rel)))
fundamental {Γ = Γ} {τ = τ} {γ = γ}
            (⇓-case-r {τ₁ = τ₁} {τ₂ = τ₂} {s = sc} {t₁ = t₁} {t₂ = t₂} {v = v} {u = u} {R = R_s} {T = T} D₁ D₂) {gi} rγ s x g rel =
  DepRel-resp τ (ValRel-resp τ (Ix.sym τ Eidx) (fundamental-val D₂ (rγ · rv'))) (λ k → ≈-sym (app-case {γ = γ} v R_s T s x k))
    (case-den τ (Ix.sym τ Eidx) Eidx s a_s (ap R_s (inputs γ s x) zero) (⟦ t₂ ⟧tm .famf .transf (gi , i') .func (g , y_v))
       (⟦ case sc t₁ t₂ ⟧tm .famf .transf gi .func g) o_s₀
       (Fib.trans τ (⟦ t₂ ⟧tm .idxf .sfunc (gi , i')) (case-fibre sc t₁ t₂ gi g (inj₂ i') e)
          (elimF-elt {⟦ Γ ⟧ctxt} {⟦ τ₂ ⟧} {⟦ τ ⟧} (ctrl-dep τ) ⟦ t₂ ⟧tm {gi} {i'} g a_s y_v)))
    (DepRel-transport τ (Ix.sym τ Eidx) (fundamental-val D₂ (rγ · rv'))
       (fundamental D₂ (_·_ {τ = τ₂} {v = v} {i = i'} rγ rv') (ap R_s (inputs γ s x) zero +ₛ (ctrl ·ₛ s)) X (g , y_v)
                              (branch-env {τk = τ₂} rγ {v = v} {i' = i'} rv' s x g (ap R_s (inputs γ s x)) y_v rel payload₁)))
  where
  rs = fundamental-val D₁ rγ
  i' = proj₁ rs
  r_v = proj₁ (proj₂ rs)
  rv' = ValRel-at-bound τ₂ r_v
  e : Ix._≈_ (τ₁ [+] τ₂) (⟦ sc ⟧tm .idxf .sfunc gi) (inj₂ i')
  e = prop.Prf.prf (proj₂ (proj₂ rs))
  Eidx : Ix._≈_ τ (⟦ case sc t₁ t₂ ⟧tm .idxf .sfunc gi) (⟦ t₂ ⟧tm .idxf .sfunc (gi , i'))
  Eidx = case-idx sc t₁ t₂ gi (inj₂ i') e
  X : ∣ 𝔽 (width-env γ + width v) ∣
  X m = ap (M.in₁ {width-env γ} {width v}) x m +ₛ ap (M.in₂ {width-env γ} {width v}) (λ m' → ap R_s (inputs γ s x) (suc m')) m
  SG = ⟦ τ₁ [+] τ₂ ⟧ .fam .subst {⟦ sc ⟧tm .idxf .sfunc gi} {inj₂ i'} e .func (⟦ sc ⟧tm .famf .transf gi .func g)
  a_s = proj₁ SG
  y_v = proj₂ SG
  split-sum = subst-ctrl-dep+ (τ₁ [+] τ₂) {⟦ sc ⟧tm .idxf .sfunc gi} {inj₂ i'} e s (⟦ sc ⟧tm .famf .transf gi .func g)

  o_s₀ : ap R_s (inputs γ s x) zero ≈s ((ctrl ·ₛ s) +ₛ a_s)
  o_s₀ = ≈-trans (proj₁ (fundamental D₁ rγ s x g rel))
                 (≈-trans (proj₁ split-sum) (+-cong (proj₁ (ctrl-dep-inj₂ {τ₁} {τ₂} i' s)) ≈-refl))

  payload₁ : DepRel τ₂ rv' (λ m → ap R_s (inputs γ s x) (suc m)) (Fib._+_ τ₂ i' y_v (ctrl-dep-at τ₂ i' s))
  payload₁ =
    DepRel-resp τ₂ rv' (λ m → ≈-refl)
      (Fib.trans τ₂ i' (proj₂ split-sum)
        (Fib.trans τ₂ i' (Fib.+-cong τ₂ i' (proj₂ (ctrl-dep-inj₂ {τ₁} {τ₂} i' s)) (Fib.refl τ₂ i')) (Fib.+-comm τ₂ i')))
      (DepRel-at-bound τ₂ r_v (proj₂ (fundamental D₁ rγ s x g rel)))
fundamental {Γ = Γ} {τ = σ [×] τ} {γ = γ} (⇓-pair {s = M} {t = N} {v = v} {u = u} {R = R₁} {T = R₂} D₁ D₂) {gi} rγ s x g rel =
  root ,
  (DepRel-at-bound σ (fundamental-val D₁ rγ)
     (DepRel-resp σ (fundamental-val D₁ rγ) (λ k → ≈-sym (comp₁ k)) den₁ (fundamental D₁ rγ s x g rel)) ,
   DepRel-at-bound τ (fundamental-val D₂ rγ)
     (DepRel-resp τ (fundamental-val D₂ rγ) (λ k → ≈-sym (comp₂ k)) den₂ (fundamental D₂ rγ s x g rel)))
  where
  i = ⟦ M ⟧tm .idxf .sfunc gi
  j = ⟦ N ⟧tm .idxf .sfunc gi
  o = ap (built-out γ (width v + width u) +ₘ (M.in₂ {1} ∘ ⟨ R₁ , R₂ ⟩)) (inputs γ s x)
  d = Fib._+_ (σ [×] τ) (i , j) (ctrl-dep-at (σ [×] τ) (i , j) s) (⟦ pair M N ⟧tm .famf .transf gi .func g)

  tail-eq : ∀ k → o (suc k) ≈s (ap (M.in₁ {width v} {width u}) (ap R₁ (inputs γ s x)) k +ₛ ap (M.in₂ {width v} {width u}) (ap R₂ (inputs γ s x)) k)
  tail-eq k =
    ≈-trans (built {γ = γ} ⟨ R₁ , R₂ ⟩ s x (suc k))
            (≈-trans (app-+ₘ (M.in₁ {width v} {width u} ∘ R₁) (M.in₂ {width v} {width u} ∘ R₂) (inputs γ s x) k)
                     (+-cong (app-∘ (M.in₁ {width v} {width u}) R₁ (inputs γ s x) k)
                             (app-∘ (M.in₂ {width v} {width u}) R₂ (inputs γ s x) k)))

  root : o zero ≈s proj₁ d
  root =
    ≈-trans (built {γ = γ} ⟨ R₁ , R₂ ⟩ s x zero)
            (≈-sym (≈-trans (+-cong (proj₁ (ctrl-dep-pair {σ} {τ} i j s)) (≈-refl {ε})) +-runit))

  comp₁ : ∀ k → ap (M.p₁ {width v} {width u}) (λ l → o (suc l)) k ≈s (ap R₁ (inputs γ s x)) k
  comp₁ k = ≈-trans (app-congᵥ (M.p₁ {width v} {width u}) tail-eq k) (ap-p₁-++ (ap R₁ (inputs γ s x)) (ap R₂ (inputs γ s x)) k)

  comp₂ : ∀ k → ap (M.p₂ {width v} {width u}) (λ l → o (suc l)) k ≈s (ap R₂ (inputs γ s x)) k
  comp₂ k = ≈-trans (app-congᵥ (M.p₂ {width v} {width u}) tail-eq k) (ap-p₂-++ (ap R₁ (inputs γ s x)) (ap R₂ (inputs γ s x)) k)

  den₁ : Fib._≈_ σ i (Fib._+_ σ i (ctrl-dep-at σ i s) (⟦ M ⟧tm .famf .transf gi .func g)) (proj₁ (proj₂ d))
  den₁ = Fib.sym σ i (Fib.+-cong σ i (proj₁ (proj₂ (ctrl-dep-pair {σ} {τ} i j s))) (Fib.+-runit σ i))

  den₂ : Fib._≈_ τ j (Fib._+_ τ j (ctrl-dep-at τ j s) (⟦ N ⟧tm .famf .transf gi .func g)) (proj₂ (proj₂ d))
  den₂ = Fib.sym τ j (Fib.+-cong τ j (proj₂ (proj₂ (ctrl-dep-pair {σ} {τ} i j s))) (Fib.+-lunit τ j))
fundamental {Γ = Γ} {τ = σ} {γ = γ} (⇓-fst {τ₂ = τ} {t = t} {v = v} {u = u} {R = R'} D) {gi} rγ s x g rel =
  DepRel-resp σ (ValRel-at-bound σ (proj₁ (fundamental-val D rγ))) (λ k → ≈-sym (proj-op {γ = γ} v {width v} {width u} (M.p₁ {width v} {width u}) R' s x k))
    (proj-den σ i s a₀ (ap R' (inputs γ s x) zero) (proj₁ (proj₂ (Fib._+_ (σ [×] τ) ij (ctrl-dep-at (σ [×] τ) ij s) (⟦ t ⟧tm .famf .transf gi .func g))))
       (⟦ fst {τ₂ = τ} t ⟧tm .famf .transf gi .func g) (proj₁ (proj₂ (⟦ t ⟧tm .famf .transf gi .func g)))
       o'₀ (Fib.+-cong σ i (proj₁ (proj₂ (ctrl-dep-pair {σ} {τ} i (proj₂ ij) s))) (Fib.refl σ i)) G-form)
    (ctrl-add σ (ValRel-at-bound σ (proj₁ (fundamental-val D rγ))) ((ctrl ·ₛ s) +ₛ ap R' (inputs γ s x) zero)
      (DepRel-at-bound σ (proj₁ (fundamental-val D rγ)) (proj₁ (proj₂ (fundamental D rγ s x g rel)))))
  where
  ij = ⟦ t ⟧tm .idxf .sfunc gi
  i = proj₁ ij
  a₀ = proj₁ (⟦ t ⟧tm .famf .transf gi .func g)
  o'₀ : ap R' (inputs γ s x) zero ≈s ((ctrl ·ₛ s) +ₛ a₀)
  o'₀ = ≈-trans (proj₁ (fundamental D rγ s x g rel)) (+-cong (proj₁ (ctrl-dep-pair {σ} {τ} i (proj₂ ij) s)) (≈-refl {a₀}))
  G-form : Fib._≈_ σ i (⟦ fst {τ₂ = τ} t ⟧tm .famf .transf gi .func g) (Fib._+_ σ i (proj₁ (proj₂ (⟦ t ⟧tm .famf .transf gi .func g))) (ctrl-dep-at σ i a₀))
  G-form = elim-elt {⟦ Γ ⟧ctxt} {Fam-P.prod ⟦ σ ⟧ ⟦ τ ⟧} {⟦ σ ⟧} (ctrl-dep σ)
             (Fam-cat._∘_ (Fam-P.p₁ {⟦ σ ⟧} {⟦ τ ⟧}) (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Fam-P.prod ⟦ σ ⟧ ⟦ τ ⟧})) ⟦ t ⟧tm {gi} g
fundamental {Γ = Γ} {τ = τ} {γ = γ} (⇓-snd {τ₁ = σ} {t = t} {v = v} {u = u} {R = R'} D) {gi} rγ s x g rel =
  DepRel-resp τ (ValRel-at-bound τ (proj₂ (fundamental-val D rγ))) (λ k → ≈-sym (proj-op {γ = γ} u {width v} {width u} (M.p₂ {width v} {width u}) R' s x k))
    (proj-den τ j s a₀ (ap R' (inputs γ s x) zero) (proj₂ (proj₂ (Fib._+_ (σ [×] τ) ij (ctrl-dep-at (σ [×] τ) ij s) (⟦ t ⟧tm .famf .transf gi .func g))))
       (⟦ snd {τ₁ = σ} t ⟧tm .famf .transf gi .func g) (proj₂ (proj₂ (⟦ t ⟧tm .famf .transf gi .func g)))
       o'₀ (Fib.+-cong τ j (proj₂ (proj₂ (ctrl-dep-pair {σ} {τ} (proj₁ ij) j s))) (Fib.refl τ j)) G-form)
    (ctrl-add τ (ValRel-at-bound τ (proj₂ (fundamental-val D rγ))) ((ctrl ·ₛ s) +ₛ ap R' (inputs γ s x) zero)
      (DepRel-at-bound τ (proj₂ (fundamental-val D rγ)) (proj₂ (proj₂ (fundamental D rγ s x g rel)))))
  where
  ij = ⟦ t ⟧tm .idxf .sfunc gi
  j = proj₂ ij
  a₀ = proj₁ (⟦ t ⟧tm .famf .transf gi .func g)
  o'₀ : ap R' (inputs γ s x) zero ≈s ((ctrl ·ₛ s) +ₛ a₀)
  o'₀ = ≈-trans (proj₁ (fundamental D rγ s x g rel)) (+-cong (proj₁ (ctrl-dep-pair {σ} {τ} (proj₁ ij) j s)) (≈-refl {a₀}))
  G-form : Fib._≈_ τ j (⟦ snd {τ₁ = σ} t ⟧tm .famf .transf gi .func g) (Fib._+_ τ j (proj₂ (proj₂ (⟦ t ⟧tm .famf .transf gi .func g))) (ctrl-dep-at τ j a₀))
  G-form = elim-elt {⟦ Γ ⟧ctxt} {Fam-P.prod ⟦ σ ⟧ ⟦ τ ⟧} {⟦ τ ⟧} (ctrl-dep τ)
             (Fam-cat._∘_ (Fam-P.p₂ {⟦ σ ⟧} {⟦ τ ⟧}) (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Fam-P.prod ⟦ σ ⟧ ⟦ τ ⟧})) ⟦ t ⟧tm {gi} g
fundamental {Γ = Γ} {τ = σ [→] τ} {γ = γ} (⇓-lam {t = t'}) {gi} rγ s x g rel =
  root , clause
  where
  o : ∣ 𝔽 (suc (width-env γ)) ∣
  o = ap (lam-out γ t') (inputs γ s x)

  o₀ : o zero ≈s (ctrl ·ₛ s)
  o₀ = ≈-trans (ap-⊕₁ {width-env γ} (ctrl-row {1}) M.I (inputs γ s x) zero) (ap-ctrl-row {1} s zero)

  o-tail : ∀ k → o (suc k) ≈s x k
  o-tail k = ≈-trans (ap-⊕₁ {width-env γ} (ctrl-row {1}) M.I (inputs γ s x) (suc k)) (app-I x k)

  f = ⟦ lam t' ⟧tm .idxf .sfunc gi

  root : o zero ≈s proj₁ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) (⟦ lam t' ⟧tm .famf .transf gi .func g))
  root = ≈-trans o₀ (≈-sym (≈-trans (+-cong (proj₁ (ctrl-dep-clo {σ} {τ} f s)) ≈-refl) +-runit))

  clause : ∀ (s' : Setoid.Carrier A) {v : Val σ} {j : Ix σ}
             (rv : ValRel′ (arr-depth σ ⊔ arr-depth τ) σ (bound₁ ≤-refl) v j)
             (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) →
             DepRel⊑′ (arr-depth σ ⊔ arr-depth τ) σ (bound₁ ≤-refl) rv (s' +ₛ o zero) z y →
           ∀ {u U} (D : γ · v , t' ⇓ u [ U ]) →
             DepRel′ (arr-depth σ ⊔ arr-depth τ) τ (bound₂ ≤-refl)
               (ValRel-at-bound τ (fundamental-val D (rγ · ValRel-at-bound σ rv)))
               (ap U (body-input γ v (s' +ₛ o zero) (λ k → o (suc k)) z))
               (Fib._+_ τ (f .idxf .sfunc j)
                 (ctrl-dep-at τ (f .idxf .sfunc j) (s' +ₛ o zero))
                 (Fib._+_ τ (f .idxf .sfunc j)
                   (evalΠ σ τ f j .func
                      (proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) (⟦ lam t' ⟧tm .famf .transf gi .func g))))
                   (f .famf .transf j .func y)))
  clause s' {v} {j} rv z y hz {u} {U} D =
    DepRel-at-bound τ (fundamental-val D (rγ · ValRel-at-bound σ rv))
      (DepRel-resp τ (fundamental-val D (rγ · ValRel-at-bound σ rv))
      (app-congᵥ U (body-input-resp γ v (+-cong ≈-refl (≈-sym o₀)) (λ k → ≈-sym (o-tail k))))
      (Fib.+-cong τ (f .idxf .sfunc j)
         (ctrl-dep τ .at (f .idxf .sfunc j) .func-resp-≈ (+-cong ≈-refl (≈-sym o₀)))
         (Fib.trans τ (f .idxf .sfunc j)
            (⟦ t' ⟧tm .famf .transf (gi , j) .func-resp-≈
               {g , y} {FibC._+_ Γ gi g (FibC.ε Γ gi) , Fib._+_ σ j (Fib.ε σ j) y}
               (FibC.sym Γ gi (FibC.+-runit Γ gi) , Fib.sym σ j (Fib.+-lunit σ j)))
         (Fib.trans τ (f .idxf .sfunc j)
            (⟦ t' ⟧tm .famf .transf (gi , j) .preserve-+
               {g , Fib.ε σ j} {FibC.ε Γ gi , y})
            (Fib.+-cong τ (f .idxf .sfunc j)
               (Fib.trans τ (f .idxf .sfunc j) (Fib.sym τ (f .idxf .sfunc j) β)
                  (evalΠ σ τ f j .func-resp-≈
                     {proj₂ L} {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) L)}
                     (Payload.sym σ τ f {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) L)} {proj₂ L}
                        (payload-ctrl-dep σ τ f s L))))
               (Fib.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))))
      (fundamental D (rγ · ValRel-at-bound σ rv) (s' +ₛ (ctrl ·ₛ s)) (λ k → body-input γ v (s' +ₛ (ctrl ·ₛ s)) x z (suc k)) (g , y)
         (EnvDepRel-resp rγ (s' +ₛ (ctrl ·ₛ s)) (λ k → ≈-sym (ap-p₁-++ x z k)) (EnvDepRel-mono rγ s s' rel) ,
          DepRel⊑-resp σ (ValRel-at-bound σ rv) (s' +ₛ (ctrl ·ₛ s)) (λ k → ≈-sym (ap-p₂-++ x z k))
            (DepRel⊑-resp-ctrl σ (ValRel-at-bound σ rv) (+-cong ≈-refl o₀) (DepRel⊑-at-bound σ rv hz)))))
    where
    L = ⟦ lam t' ⟧tm .famf .transf gi .func g

    β : Fib._≈_ τ (f .idxf .sfunc j)
          (evalΠ σ τ f j .func (proj₂ L))
          (⟦ t' ⟧tm .famf .transf (gi , j) .func (g , Fib.ε σ j))
    Fλ : indexed-family.constantFam (⟦ σ ⟧ .idx) SemiMod.cat (FibC Γ gi)
           indexed-family.⇒f (⟦ τ ⟧ .fam indexed-family.[ f .idxf ])
    Fλ = indexed-family._∘f_ indexed-family.reindex-comp
           (indexed-family._∘f_ (indexed-family.reindex-f (model.exp.nudge gi) (⟦ t' ⟧tm .famf))
                                (model.exp.nudge-in₁ gi))
    β = ΠP.lambda-eval {A = ⟦ σ ⟧ .idx} {P = ⟦ τ ⟧ .fam indexed-family.[ f .idxf ]} {x = FibC Γ gi} {f = Fλ} j
          .func-eq (FibC.refl Γ gi {g})
fundamental {Γ = Γ} {τ = τ} {γ = γ}
            (⇓-app {Γ' = Γ'} {σ = σ} {γ' = γ'} {s = M} {t = N} {t' = t'} {v = v} {u = u} {R = R} {T = T} {U = U} D₁ D₂ D₃) {gi} rγ s x g rel =
  DepRel-resp τ (ValRel-at-bound τ (fundamental-val D₁ rγ (ValRel-at-bound σ (fundamental-val D₂ rγ)) D₃))
    (λ k → ≈-sym (app-op k)) den-eq
    (DepRel-at-bound τ (fundamental-val D₁ rγ (ValRel-at-bound σ (fundamental-val D₂ rγ)) D₃) C)
  where
  f = ⟦ M ⟧tm .idxf .sfunc gi
  j = ⟦ N ⟧tm .idxf .sfunc gi
  i₁ = f .idxf .sfunc j
  m = proj₂ (⟦ M ⟧tm .famf .transf gi .func g)
  yN = ⟦ N ⟧tm .famf .transf gi .func g
  o : ∣ 𝔽 (suc (width-env γ')) ∣
  o = ap R (inputs γ s x)
  z : ∣ 𝔽 (width v) ∣
  z = ap T (inputs γ s x)

  o₀ : o zero ≈s ((ctrl ·ₛ s) +ₛ (proj₁ (⟦ M ⟧tm .famf .transf gi .func g)))
  o₀ = ≈-trans (proj₁ (fundamental D₁ rγ s x g rel)) (+-cong (proj₁ (ctrl-dep-clo {σ} {τ} f s)) ≈-refl)

  arg : DepRel⊑′ (arr-depth σ ⊔ arr-depth τ) σ (bound₁ ≤-refl)
          (ValRel-at-bound σ (fundamental-val D₂ rγ)) ((ctrl ·ₛ s) +ₛ o zero) z yN
  arg = DepRel⊑-at-bound σ (fundamental-val D₂ rγ)
          (ctrl-dep-at σ j s ,
           (Fib.⊑-trans σ j (⊑ctrl-dep-mono σ j s (o zero) _ (Fib.⊑-refl σ j))
                          (Fib.≈→⊑ σ j (ctrl-dep σ .at j .func-resp-≈ +-comm)) ,
            DepRel-resp σ (fundamental-val D₂ rγ) (λ k → ≈-refl) (Fib.+-comm σ j) (fundamental D₂ rγ s x g rel)))

  C : DepRel′ (arr-depth σ ⊔ arr-depth τ) τ (bound₂ ≤-refl)
        (fundamental-val D₁ rγ (ValRel-at-bound σ (fundamental-val D₂ rγ)) D₃)
        (ap U (body-input γ' v ((ctrl ·ₛ s) +ₛ o zero) (λ l → o (suc l)) z))
        (Fib._+_ τ i₁ (ctrl-dep-at τ i₁ ((ctrl ·ₛ s) +ₛ o zero))
          (Fib._+_ τ i₁ (evalΠ σ τ f j .func (proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) (⟦ M ⟧tm .famf .transf gi .func g))))
                      (f .famf .transf j .func yN)))
  C = proj₂ (fundamental D₁ rγ s x g rel) (ctrl ·ₛ s) (ValRel-at-bound σ (fundamental-val D₂ rγ)) z yN arg D₃

  den-eq : Fib._≈_ τ i₁
             (Fib._+_ τ i₁ (ctrl-dep-at τ i₁ ((ctrl ·ₛ s) +ₛ o zero))
               (Fib._+_ τ i₁ (evalΠ σ τ f j .func (proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) (⟦ M ⟧tm .famf .transf gi .func g))))
                           (f .famf .transf j .func yN)))
             (Fib._+_ τ i₁ (ctrl-dep-at τ i₁ s) (⟦ app M N ⟧tm .famf .transf gi .func g))
  den-eq =
    Fib.trans τ i₁ (Fib.+-cong τ i₁ ctrl-dep-part (Fib.+-cong τ i₁ eval-part (Fib.refl τ i₁)))
    (Fib.trans τ i₁ (Fib.+-assoc τ i₁)
                  (Fib.+-cong τ i₁ (Fib.refl τ i₁) (Fib.trans τ i₁ (Fib.+-comm τ i₁) (Fib.sym τ i₁ G-form))))
    where
    G-form : Fib._≈_ τ i₁ (⟦ app M N ⟧tm .famf .transf gi .func g)
               (Fib._+_ τ i₁ (Fib._+_ τ i₁ (evalΠ σ τ f j .func m) (f .famf .transf j .func yN)) (ctrl-dep-at τ i₁ (proj₁ (⟦ M ⟧tm .famf .transf gi .func g))))
    G-form =
      Fib.trans τ i₁ (elim-elt {⟦ Γ ⟧ctxt} {Ex} {⟦ τ ⟧} (ctrl-dep τ) body ⟦ M ⟧tm {gi} g)
                   (Fib.+-cong τ i₁ (HasExponentials.eval model.SemiModExp {⟦ σ ⟧} {⟦ τ ⟧} .famf .transf (f , j) .func-resp-≈
                                      {Fam-P.pair (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Ex})
                                         (Fam-cat._∘_ ⟦ N ⟧tm (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Ex})) .famf .transf (gi , f) .func (g , m)}
                                      {m , yN}
                                      (Fpair-elt {Fam-P.prod ⟦ Γ ⟧ctxt Ex} {Ex} {⟦ σ ⟧}
                                         (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Ex})
                                         (Fam-cat._∘_ ⟦ N ⟧tm (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Ex})) (gi , f) (g , m)))
                                  (Fib.refl τ i₁))
      where
      Ex = HasExponentials.exp model.SemiModExp ⟦ σ ⟧ ⟦ τ ⟧
      body = Fam-cat._∘_ (HasExponentials.eval model.SemiModExp {⟦ σ ⟧} {⟦ τ ⟧})
               (Fam-P.pair (Fam-P.p₂ {⟦ Γ ⟧ctxt} {Ex})
                                             (Fam-cat._∘_ ⟦ N ⟧tm (Fam-P.p₁ {⟦ Γ ⟧ctxt} {Ex})))

    ctrl-dep-part : Fib._≈_ τ i₁ (ctrl-dep-at τ i₁ ((ctrl ·ₛ s) +ₛ o zero)) (Fib._+_ τ i₁ (ctrl-dep-at τ i₁ s) (ctrl-dep-at τ i₁ (proj₁ (⟦ M ⟧tm .famf .transf gi .func g))))
    ctrl-dep-part = ctrl-dep-split τ i₁ s (proj₁ (⟦ M ⟧tm .famf .transf gi .func g)) o₀

    eval-part : Fib._≈_ τ i₁ (evalΠ σ τ f j .func (proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) (⟦ M ⟧tm .famf .transf gi .func g))))
                           (evalΠ σ τ f j .func m)
    eval-part = evalΠ σ τ f j .func-resp-≈ {proj₂ (Fib._+_ (σ [→] τ) f (ctrl-dep-at (σ [→] τ) f s) (⟦ M ⟧tm .famf .transf gi .func g))} {m}
                  (payload-ctrl-dep σ τ f s (⟦ M ⟧tm .famf .transf gi .func g))

  app-op : ∀ k → ap (U ∘ (body-inputs γ γ' v ∘ ⟨ ⟨ M.I , R ⟩ , T ⟩)) (inputs γ s x) k
                 ≈s ap U (body-input γ' v ((ctrl ·ₛ s) +ₛ o zero) (λ l → o (suc l)) z) k
  app-op k =
    ≈-trans (app-∘ U (body-inputs γ γ' v ∘ ⟨ ⟨ M.I , R ⟩ , T ⟩) (inputs γ s x) k)
            (app-congᵥ U (ap-body-inputs γ γ' v R T s x) k)
fundamental {Γ = Γ} {τ = μ τ} {γ = γ} (⇓-roll {t = t} {v = v} {R = R} D) {gi} rγ s x g rel =
  DepRel-at-bound (τ [ μ τ ]) (ValRel-resp (τ [ μ τ ]) e r)
    (DepRel-resp (τ [ μ τ ]) (ValRel-resp (τ [ μ τ ]) e r) (λ k → ≈-refl) ed
      (DepRel-transport (τ [ μ τ ]) e r (fundamental D rγ s x g rel)))
  where
  r  = fundamental-val D rγ
  i  = ⟦ t ⟧tm .idxf .sfunc gi
  I  = roll-mor τ .idxf .sfunc i
  i₂ = unroll-mor τ .idxf .sfunc I
  G  = ⟦ t ⟧tm .famf .transf gi .func g
  X' = unroll-mor τ .famf .transf I .func (roll-mor τ .famf .transf i .func G)
  e₀ : Ix._≈_ (τ [ μ τ ]) i₂ i
  e₀ = idx-eq (unroll-roll τ) i
  e : Ix._≈_ (τ [ μ τ ]) i i₂
  e = Ix.sym (τ [ μ τ ]) {i₂} {i} e₀

  tr-eq : Fib._≈_ (τ [ μ τ ]) i (⟦ τ [ μ τ ] ⟧ .fam .subst e₀ .func X') G
  tr-eq = unroll-roll τ ._≃_.famf-eq .indexed-family._≃f_.transf-eq {i}
            .func-eq (Fib.refl (τ [ μ τ ]) i {G})

  chainX : Fib._≈_ (τ [ μ τ ]) i₂ X' (⟦ τ [ μ τ ] ⟧ .fam .subst e .func G)
  chainX =
    Fib.trans (τ [ μ τ ]) i₂
      (Fib.sym (τ [ μ τ ]) i₂ (subst-refl ⟦ τ [ μ τ ] ⟧ {i₂} (Ix.trans (τ [ μ τ ]) {i₂} {i} {i₂} e₀ e) X'))
    (Fib.trans (τ [ μ τ ]) i₂
      (subst-trans ⟦ τ [ μ τ ] ⟧ {i₂} {i} {i₂} e₀ e X')
      (⟦ τ [ μ τ ] ⟧ .fam .subst e .func-resp-≈ tr-eq))

  ed : Fib._≈_ (τ [ μ τ ]) i₂
         (⟦ τ [ μ τ ] ⟧ .fam .subst e .func (Fib._+_ (τ [ μ τ ]) i (ctrl-dep-at (τ [ μ τ ]) i s) G))
         (unroll-mor τ .famf .transf I .func
           (Fib._+_ (μ τ) I (ctrl-dep-at (μ τ) I s) (roll-mor τ .famf .transf i .func G)))
  ed =
    Fib.trans (τ [ μ τ ]) i₂ (subst-ctrl-dep+ (τ [ μ τ ]) {i} {i₂} e s G)
    (Fib.trans (τ [ μ τ ]) i₂
      (Fib.+-cong (τ [ μ τ ]) i₂ (Fib.refl (τ [ μ τ ]) i₂) (Fib.sym (τ [ μ τ ]) i₂ chainX))
      (Fib.sym (τ [ μ τ ]) i₂
        (Fib.trans (τ [ μ τ ]) i₂
          (unroll-mor τ .famf .transf I .preserve-+
            {ctrl-dep-at (μ τ) I s} {roll-mor τ .famf .transf i .func G})
          (Fib.+-cong (τ [ μ τ ]) i₂
            (preserves-unroll-ctrl-dep τ .at I .func-eq {s} {s} ≈-refl)
            (Fib.refl (τ [ μ τ ]) i₂)))))
fundamental {Γ = Γ} {γ = γ} (⇓-fold {τ = τ₀} {σ = σ} {s = s} {t = t} {R = R} {F = F} D M) {gi} rγ w x g rel =
  DepRel-resp σ (ValRel-resp σ E rv') (λ k → ≈-sym (in-eq k)) fib-eq
    (DepRel-transport σ E rv'
      (map-dep (λ D' rγ' → fundamental-val D' rγ')
        (λ D' rγ' w' x' g' rel' → fundamental D' rγ' w' x' g' rel')
        M rγ {i = it} rv w x g rel (ap R y) dt hd))
  where
  it = ⟦ t ⟧tm .idxf .sfunc gi
  Fv = fold-map τ₀ σ (var zero) ⟦ s ⟧tm
  IF = Fv .idxf .sfunc (gi , it)
  J = ⟦ fold s t ⟧tm .idxf .sfunc gi
  E = idx-eq (fold-map-var τ₀ σ ⟦ s ⟧tm) (gi , it)
  rv = fundamental-val D rγ
  rv' = map-val {s = s} (λ D' rγ' → fundamental-val D' rγ') M rγ {i = it} rv
  y = inputs γ w x
  dt = ⟦ t ⟧tm .famf .transf gi .func g
  dF = Fv .famf .transf (gi , it) .func (g , dt)
  hd = fundamental D rγ w x g rel
  in-eq : ∀ k → ap (F ∘ ⟨ M.I , R ⟩) y k ≈s ap F (map-input γ w x (ap R y)) k
  in-eq k =
    ≈-trans (app-∘ F ⟨ M.I , R ⟩ y k)
      (app-congᵥ F (λ l →
         ≈-trans (app-pair M.I R y l)
         (≈-trans (M.concat-preserves _≈s_ {u₁ = ap M.I y} {u₂ = y} {v₁ = ap R y} {v₂ = ap R y}
                     (app-I y) (λ j → ≈-refl) l)
                  (≈-sym (≈-trans (+-cong (app-in₁ y l) (app-in₂ (ap R y) l)) (concat-pad y (ap R y) l))))) k)
  fib-eq : Fib._≈_ σ J
             (⟦ σ ⟧ .fam .subst {IF} {J} E .func (Fib._+_ σ IF (ctrl-dep-at σ IF w) dF))
             (Fib._+_ σ J (ctrl-dep-at σ J w) (⟦ fold s t ⟧tm .famf .transf gi .func g))
  fib-eq =
    Fib.trans σ J (subst-ctrl-dep+ σ {IF} {J} E w dF)
      (Fib.+-cong σ J (Fib.refl σ J) (fold-fibre {τ₀ = τ₀} s t gi g))
fundamental {Γ = Γ} {τ = base o} {γ = γ} (⇓-bop {is = is} {ω = ω} {Ms = Ms} {vs = vs} {R = Rs} D) {gi} rγ s x g rel k =
  ≈-trans (app-+ₘ wctrl (op-deps ω .sfunc vs ∘ Rs) (inputs γ s x) k)
  (≈-trans (+-cong (ap-wctrl {width-env γ} {sort-width o} (inputs γ s x) k)
                   (≈-trans (app-∘ (op-deps ω .sfunc vs) Rs (inputs γ s x) k)
                   (≈-trans (app-congᵥ (op-deps ω .sfunc vs) IH k)
                   (≈-trans (app-+ (op-deps ω .sfunc vs) (λ _ → ctrl ·ₛ s) (args-vec Ms gi g) k)
                            (+-cong (≈-trans (app-congᵥ (op-deps ω .sfunc vs) (λ _ → ≈-sym ·-runit) k)
                                             (≈-trans (model.app-· (op-deps ω .sfunc vs) (ctrl ·ₛ s) (λ _ → ι) k) (·-cong ·-comm ≈-refl)))
                                    ≈-refl)))))
  (≈-trans (≈-sym +-assoc)
  (≈-trans (+-cong (cs-absorb s (ap (op-deps ω .sfunc vs) (λ _ → ι) k)) ≈-refl)
           (+-cong (≈-sym (ctrl-dep-base (⟦ bop ω Ms ⟧tm .idxf .sfunc gi) s k)) (≈-sym den)))))
  where
  C = collect is .Fam⟨𝒞⟩μ.famf .transf (𝒟-arg-product is .idxf .sfunc (⟦ Ms ⟧tms .idxf .sfunc gi))
  tp-elt = 𝒟-arg-product is .famf .transf (⟦ Ms ⟧tms .idxf .sfunc gi) .func (⟦ Ms ⟧tms .famf .transf gi .func g)
  IH : ∀ l → ap Rs (inputs γ s x) l ≈s ((ctrl ·ₛ s) +ₛ (args-vec Ms gi g) l)
  IH = fundamental-s D rγ s x g rel
  den : ⟦ bop ω Ms ⟧tm .famf .transf gi .func g k ≈s ap (op-deps ω .sfunc vs) (args-vec Ms gi g) k
  den = ≈-trans (app-∘ M.I (op-deps ω .sfunc (args-idx Ms gi) ∘ C) tp-elt k)
        (≈-trans (app-I (ap (op-deps ω .sfunc (args-idx Ms gi) ∘ C) tp-elt) k)
        (≈-trans (app-∘ (op-deps ω .sfunc (args-idx Ms gi)) C tp-elt k)
                 (app-congₘ (op-deps ω .sfunc-resp-≈ (Prf.prf (fundamental-vals D rγ))) (args-vec Ms gi g) k)))
fundamental {Γ = Γ} {γ = γ} (⇓-brel {is = is} {ω = ω} {Ms = Ms} {vs = vs} {R = Rs} D) {gi} rγ s x g rel =
  DepRel-bool ω vs b {i} e (ap (wctrl +ₘ (brel-deps ω vs b ∘ Rs)) (inputs γ s x))
    (Fib._+_ (unit [+] unit) i (ctrl-dep-at (unit [+] unit) i s) (⟦ brel ω Ms ⟧tm .famf .transf gi .func g)) s (args-vec Ms gi g) op-side model-side
  where
  b = rel-pred ω .sfunc vs
  i = ⟦ brel ω Ms ⟧tm .idxf .sfunc gi
  e = brel-idx ω Ms gi vs (Prf.prf (fundamental-vals D rγ))
  IH : ∀ l → ap Rs (inputs γ s x) l ≈s ((ctrl ·ₛ s) +ₛ (args-vec Ms gi g) l)
  IH = fundamental-s D rγ s x g rel
  op-side : ∀ k → ap (wctrl +ₘ (brel-deps ω vs b ∘ Rs)) (inputs γ s x) k
                  ≈s ((ctrl ·ₛ s) +ₛ ap (brel-deps ω vs b) (λ l → (ctrl ·ₛ s) +ₛ (args-vec Ms gi g) l) k)
  op-side k =
    ≈-trans (app-+ₘ wctrl (brel-deps ω vs b ∘ Rs) (inputs γ s x) k)
            (+-cong (ap-wctrl {width-env γ} {width (bool→val b)} (inputs γ s x) k)
                    (≈-trans (app-∘ (brel-deps ω vs b) Rs (inputs γ s x) k) (app-congᵥ (brel-deps ω vs b) IH k)))
  model-side : Fib._≈_ (unit [+] unit) b
                 (⟦ unit [+] unit ⟧ .fam .subst {i} {b} e .func (Fib._+_ (unit [+] unit) i (ctrl-dep-at (unit [+] unit) i s) (⟦ brel ω Ms ⟧tm .famf .transf gi .func g)))
                 (Fib._+_ (unit [+] unit) b (ctrl-dep-at (unit [+] unit) b s) (interp.bool-elt b (ap (rel-deps ω .sfunc vs) (args-vec Ms gi g) zero)))
  model-side =
    Fib.trans (unit [+] unit) b (⟦ unit [+] unit ⟧ .fam .subst {i} {b} e .preserve-+ {ctrl-dep-at (unit [+] unit) i s} {(⟦ brel ω Ms ⟧tm .famf .transf gi .func g)})
      (Fib.+-cong (unit [+] unit) b (ctrl-dep-natural (unit [+] unit) {i} {b} e s)
        (Fib.trans (unit [+] unit) b
          (interp.test.test-elt ω (⟦ Ms ⟧tms .idxf .sfunc gi) (⟦ Ms ⟧tms .famf .transf gi .func g) b e)
          (interp.bool-elt-cong b (app-congₘ (rel-deps ω .sfunc-resp-≈ (Prf.prf (fundamental-vals D rγ))) (args-vec Ms gi g) zero))))

fundamental-s [] rγ s x g rel ()
fundamental-s {γ = γ} (_∷_ {i = i} {is = is} {v = v} {R = R₁} {Rs = Rs} {M = M} {Ms = Ms} D Ds) {gi}
              rγ s x g rel k =
  ≈-trans (app-+ₘ (u₁ ∘ R₁) (u₂ ∘ Rs) (inputs γ s x) k)
  (≈-trans (+-cong (≈-trans (app-∘ u₁ R₁ (inputs γ s x) k)
                            (≈-trans (app-congᵥ u₁ IH₁ k) (app-+ u₁ (λ _ → ctrl ·ₛ s) (⟦ M ⟧tm .famf .transf gi .func g) k)))
                   (≈-trans (app-∘ u₂ Rs (inputs γ s x) k)
                            (≈-trans (app-congᵥ u₂ IH₂ k) (app-+ u₂ (λ _ → ctrl ·ₛ s) (args-vec Ms gi g) k))))
  (≈-trans S.+-interchange
           (+-cong (in-const {sort-width i} {bases-width is} (ctrl ·ₛ s) k)
                   (≈-sym (args-vec-cons M Ms gi g k)))))
  where
  u₁ = M.in₁ {sort-width i} {bases-width is}
  u₂ = M.in₂ {sort-width i} {bases-width is}
  IH₁ : ∀ l → ap R₁ (inputs γ s x) l ≈s ((ctrl ·ₛ s) +ₛ (⟦ M ⟧tm .famf .transf gi .func g) l)
  IH₁ l = ≈-trans (fundamental D rγ s x g rel l) (+-cong (ctrl-dep-base (⟦ M ⟧tm .idxf .sfunc gi) s l) ≈-refl)
  IH₂ : ∀ l → ap Rs (inputs γ s x) l ≈s ((ctrl ·ₛ s) +ₛ (args-vec Ms gi g) l)
  IH₂ = fundamental-s Ds rγ s x g rel

unroll-roll-idx : ∀ τ (i : Ix (τ [ μ τ ])) →
                  Ix._≈_ (τ [ μ τ ]) i (unroll-mor τ .idxf .sfunc (roll-mor τ .idxf .sfunc i))
unroll-roll-idx τ i =
  Ix.sym (τ [ μ τ ]) {unroll-mor τ .idxf .sfunc (roll-mor τ .idxf .sfunc i)} {i} (idx-eq (unroll-roll τ) i)

val-rel : ∀ {τ} (fo : first-order τ) (v : Val τ) → ValRel τ v (val-idx v)
val-rel unit          unit       = tt
val-rel (base s)      (const a)  = ⟪ Setoid.refl (sort-index s) ⟫
val-rel {τ₁ [+] τ₂} (fo₁ [+] fo₂) (inl v) =
  val-idx v , ValRel-at-bound τ₁ (val-rel fo₁ v) , ⟪ Ix.refl (τ₁ [+] τ₂) {inj₁ (val-idx v)} ⟫
val-rel {τ₁ [+] τ₂} (fo₁ [+] fo₂) (inr v) =
  val-idx v , ValRel-at-bound τ₂ (val-rel fo₂ v) , ⟪ Ix.refl (τ₁ [+] τ₂) {inj₂ (val-idx v)} ⟫
val-rel {τ₁ [×] τ₂} (fo₁ [×] fo₂) (pair v u) =
  ValRel-at-bound τ₁ (val-rel fo₁ v) , ValRel-at-bound τ₂ (val-rel fo₂ u)
val-rel {μ τ} (μ fo) (roll v) =
  ValRel-resp′ (τ [ μ τ ]) (bound-μ τ ≤-refl) {v} {i} {unroll-mor τ .idxf .sfunc (roll-mor τ .idxf .sfunc i)}
    (unroll-roll-idx τ i)
    (ValRel-at-bound (τ [ μ τ ]) (val-rel (fo-inst fo (μ fo)) v))
  where i = val-idx v

env-rel : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) (γ : Env Γ) → EnvValRel γ (env-idx γ)
env-rel emp         emp     = emp
env-rel (Γ-fo ▸ fo) (γ · v) = env-rel Γ-fo γ · val-rel fo v

val-rel-unique : ∀ {τ} (fo : first-order τ) {v : Val τ} {i : Ix τ} → ValRel τ v i → Ix._≈_ τ i (val-idx v)
val-rel-unique unit          {unit}      r = prop.tt
val-rel-unique (base s)      {const a}   ⟪ e ⟫ = e
val-rel-unique {τ₁ [+] τ₂} (fo₁ [+] fo₂) {inl v} {i} (i' , r , ⟪ e ⟫) =
  Ix.trans (τ₁ [+] τ₂) {i} {inj₁ i'} {inj₁ (val-idx v)} e (val-rel-unique fo₁ (ValRel-at-bound τ₁ r))
val-rel-unique {τ₁ [+] τ₂} (fo₁ [+] fo₂) {inr v} {i} (i' , r , ⟪ e ⟫) =
  Ix.trans (τ₁ [+] τ₂) {i} {inj₂ i'} {inj₂ (val-idx v)} e (val-rel-unique fo₂ (ValRel-at-bound τ₂ r))
val-rel-unique {τ₁ [×] τ₂} (fo₁ [×] fo₂) {pair v u} {i , j} (r , r') =
  val-rel-unique fo₁ (ValRel-at-bound τ₁ r) , val-rel-unique fo₂ (ValRel-at-bound τ₂ r')
val-rel-unique {μ τ} (μ fo) {roll v} {i} r =
  Ix.trans (μ τ) {i} {roll-mor τ .idxf .sfunc (unroll-mor τ .idxf .sfunc i)} {roll-mor τ .idxf .sfunc j}
    (Ix.sym (μ τ) {roll-mor τ .idxf .sfunc (unroll-mor τ .idxf .sfunc i)} {i} (idx-eq (roll-unroll τ) i))
    (roll-mor τ .idxf .sfunc-resp-≈ {unroll-mor τ .idxf .sfunc i} {j}
      (val-rel-unique (fo-inst fo (μ fo)) {v} {unroll-mor τ .idxf .sfunc i} (ValRel-at-bound (τ [ μ τ ]) r)))
  where j = val-idx v

private
  lookup-idx : ∀ {Γ τ} (x : Γ ∋ τ) (γ : Env Γ) →
               Ix._≈_ τ (⟦ var x ⟧tm .idxf .sfunc (env-idx γ)) (val-idx (lookup x γ))
  lookup-idx {τ = τ} zero     (γ · v) = Ix.refl τ {val-idx v}
  lookup-idx         (succ x) (γ · v) = lookup-idx x γ

  bool-val-idx : ∀ b → Ix._≈_ (unit [+] unit) b (val-idx (bool→val b))
  bool-val-idx (inj₁ _) = prop.tt
  bool-val-idx (inj₂ _) = prop.tt

  val-idx-cast : ∀ {τ τ'} (e : τ ≡ τ') (v : Val τ) →
                 Ix._≈_ τ' (val-idx (≡-subst Val e v)) (ty-cast e .idxf .sfunc (val-idx v))
  val-idx-cast {τ} refl v = Ix.refl τ {val-idx v}

soundness-val : ∀ {Γ τ} {t : Γ ⊢ τ} {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ]) →
                Ix._≈_ τ (⟦ t ⟧tm .idxf .sfunc (env-idx γ)) (val-idx v)
soundness-vals : ∀ {Γ is} {Ms : Every (λ σ → Γ ⊢ base σ) is} {γ : Env Γ} {vs R}
                 (D : γ , Ms ⇓s vs [ R ]) →
                 Prf (Setoid._≈_ (sort-vals-setoid sort-index is) (args-idx Ms (env-idx γ)) vs)
map-idx : ∀ {Γ} {γ : Env Γ} {τ₀ : type 1} {σr : type 0} {s : Γ ▸ τ₀ [ σr ] ⊢ σr}
          {σ' : type 1} {v : Val (σ' [ μ τ₀ ])} {v' : Val (σ' [ σr ])}
          {F : M.Matrix (width v') (suc (width-env γ) + width v)} (M : Map γ s σ' v v' F) →
          Ix._≈_ (σ' [ σr ]) (fold-map τ₀ σr σ' ⟦ s ⟧tm .idxf .sfunc (env-idx γ , val-idx v)) (val-idx v')

soundness-val (⇓-var x) = lookup-idx x _
soundness-val ⇓-unit = prop.tt
soundness-val (⇓-inl D) = soundness-val D
soundness-val (⇓-inr D) = soundness-val D
soundness-val {τ = τ} {γ = γ} (⇓-case-l {s = s} {t₁ = t₁} {t₂ = t₂} {v = v} {u = u} D₁ D₂) =
  Ix.trans τ {⟦ case s t₁ t₂ ⟧tm .idxf .sfunc gi} {⟦ t₁ ⟧tm .idxf .sfunc (gi , val-idx v)} {val-idx u}
    (case-idx s t₁ t₂ gi (inj₁ (val-idx v)) (soundness-val D₁)) (soundness-val D₂)
  where gi = env-idx γ
soundness-val {τ = τ} {γ = γ} (⇓-case-r {s = s} {t₁ = t₁} {t₂ = t₂} {v = v} {u = u} D₁ D₂) =
  Ix.trans τ {⟦ case s t₁ t₂ ⟧tm .idxf .sfunc gi} {⟦ t₂ ⟧tm .idxf .sfunc (gi , val-idx v)} {val-idx u}
    (case-idx s t₁ t₂ gi (inj₂ (val-idx v)) (soundness-val D₁)) (soundness-val D₂)
  where gi = env-idx γ
soundness-val (⇓-pair D₁ D₂) = soundness-val D₁ , soundness-val D₂
soundness-val (⇓-fst D) = proj₁ (soundness-val D)
soundness-val (⇓-snd D) = proj₂ (soundness-val D)
soundness-val {γ = γ} (⇓-lam {σ = σ} {τ = τ} {t = t}) = Ix.refl (σ [→] τ) {⟦ lam t ⟧tm .idxf .sfunc (env-idx γ)}
soundness-val {γ = γ} (⇓-app {Γ' = Γ'} {σ = σ} {τ = τ} {γ' = γ'} {s = s} {t = t} {t' = t'} {v = v} {u = u} D₁ D₂ D₃) =
  Ix.trans τ {⟦ app s t ⟧tm .idxf .sfunc gi} {⟦ t' ⟧tm .idxf .sfunc (gi' , j)} {val-idx u}
    (idx-eq-at σ τ {⟦ s ⟧tm .idxf .sfunc gi} {val-idx (clo γ' t')} (soundness-val D₁) j)
    (Ix.trans τ {⟦ t' ⟧tm .idxf .sfunc (gi' , j)} {⟦ t' ⟧tm .idxf .sfunc (gi' , val-idx v)} {val-idx u}
      (⟦ t' ⟧tm .idxf .sfunc-resp-≈ {gi' , j} {gi' , val-idx v} (IxC.refl Γ' {gi'} , soundness-val D₂))
      (soundness-val D₃))
  where
  gi  = env-idx γ
  gi' = env-idx γ'
  j   = ⟦ t ⟧tm .idxf .sfunc gi
soundness-val (⇓-bop {ω = ω} D) = op-fun ω .sfunc-resp-≈ (Prf.prf (soundness-vals D))
soundness-val {γ = γ} (⇓-brel {ω = ω} {Ms = Ms} {vs = vs} D) =
  Ix.trans (unit [+] unit) {⟦ brel ω Ms ⟧tm .idxf .sfunc gi} {b} {val-idx (bool→val b)}
    (brel-idx ω Ms gi vs (Prf.prf (soundness-vals D))) (bool-val-idx b)
  where
  gi = env-idx γ
  b  = rel-pred ω .sfunc vs
soundness-val {γ = γ} (⇓-roll {τ = τ} {t = t} {v = v} D) =
  roll-mor τ .idxf .sfunc-resp-≈ {⟦ t ⟧tm .idxf .sfunc (env-idx γ)} {val-idx v} (soundness-val D)
soundness-val {Γ} {γ = γ} (⇓-fold {τ = τ₀} {σ = σ} {s = s} {t = t} {v = v} {u = u} D M) =
  Ix.trans σ {⟦ fold s t ⟧tm .idxf .sfunc gi} {Fv .idxf .sfunc (gi , j)} {val-idx u}
    (Ix.sym σ {Fv .idxf .sfunc (gi , j)} {⟦ fold s t ⟧tm .idxf .sfunc gi}
      (idx-eq (fold-map-var τ₀ σ ⟦ s ⟧tm) (gi , j)))
    (Ix.trans σ {Fv .idxf .sfunc (gi , j)} {Fv .idxf .sfunc (gi , val-idx v)} {val-idx u}
      (Fv .idxf .sfunc-resp-≈ {gi , j} {gi , val-idx v} (IxC.refl Γ {gi} , soundness-val D))
      (map-idx M))
  where
  gi = env-idx γ
  j  = ⟦ t ⟧tm .idxf .sfunc gi
  Fv = fold-map τ₀ σ (var zero) ⟦ s ⟧tm

soundness-vals [] = ⟪ prop.tt ⟫
soundness-vals (D ∷ Ds) = ⟪ soundness-val D , Prf.prf (soundness-vals Ds) ⟫

map-idx {Γ} {γ} {τ₀} {σr} {s} (m-rec {w = w} {w' = w'} {u = u} M D) =
  Ix.trans σr {Fv .idxf .sfunc (gi , val-idx (roll {τ = τ₀} w))} {⟦ s ⟧tm .idxf .sfunc (gi , Fτ .idxf .sfunc (gi , val-idx w))} {val-idx u}
    (idx-eq (fold-map-rec τ₀ σr ⟦ s ⟧tm) (gi , val-idx w))
    (Ix.trans σr {⟦ s ⟧tm .idxf .sfunc (gi , Fτ .idxf .sfunc (gi , val-idx w))} {⟦ s ⟧tm .idxf .sfunc (gi , val-idx w')} {val-idx u}
      (⟦ s ⟧tm .idxf .sfunc-resp-≈ {gi , Fτ .idxf .sfunc (gi , val-idx w)} {gi , val-idx w'} (IxC.refl Γ {gi} , map-idx M))
      (soundness-val D))
  where
  gi = env-idx γ
  Fv = fold-map τ₀ σr (var zero) ⟦ s ⟧tm
  Fτ = fold-map τ₀ σr τ₀ ⟦ s ⟧tm
map-idx {γ = γ} {τ₀} {σr} {s} (m-unit {v = v}) = idx-eq (fold-map-unit τ₀ σr ⟦ s ⟧tm) (env-idx γ , val-idx v)
map-idx {γ = γ} {τ₀} {σr} {s} (m-base {b = b} {v = v}) = idx-eq (fold-map-base τ₀ σr b ⟦ s ⟧tm) (env-idx γ , val-idx v)
map-idx {γ = γ} {τ₀} {σr} {s} (m-arrow {σ₁ = σ₁} {σ₂ = σ₂} {v = v}) =
  idx-eq (fold-map-arrow τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (env-idx γ , val-idx v)
map-idx {γ = γ} {τ₀} {σr} {s} (m-inl {σ₁ = σ₁} {σ₂ = σ₂} {v = v} {v' = v'} M) =
  Ix.trans ((σ₁ [+] σ₂) [ σr ]) {F₊ .idxf .sfunc (gi , inj₁ (val-idx v))} {inj₁ (F₁ .idxf .sfunc (gi , val-idx v))} {inj₁ (val-idx v')}
    (idx-eq (fold-map-inl τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , val-idx v)) (map-idx M)
  where
  gi = env-idx γ
  F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
  F₁ = fold-map τ₀ σr σ₁ ⟦ s ⟧tm
map-idx {γ = γ} {τ₀} {σr} {s} (m-inr {σ₁ = σ₁} {σ₂ = σ₂} {v = v} {v' = v'} M) =
  Ix.trans ((σ₁ [+] σ₂) [ σr ]) {F₊ .idxf .sfunc (gi , inj₂ (val-idx v))} {inj₂ (F₂ .idxf .sfunc (gi , val-idx v))} {inj₂ (val-idx v')}
    (idx-eq (fold-map-inr τ₀ σr σ₁ σ₂ ⟦ s ⟧tm) (gi , val-idx v)) (map-idx M)
  where
  gi = env-idx γ
  F₊ = fold-map τ₀ σr (σ₁ [+] σ₂) ⟦ s ⟧tm
  F₂ = fold-map τ₀ σr σ₂ ⟦ s ⟧tm
map-idx {γ = γ} {τ₀} {σr} {s} (m-pair {σ₁ = σ₁} {σ₂ = σ₂} {v = v} {v' = v'} {u = u} {u' = u'} M₁ M₂) =
  Ix.trans ((σ₁ [×] σ₂) [ σr ]) {F× .idxf .sfunc (gi , (val-idx v , val-idx u))}
    {F₁ .idxf .sfunc (gi , val-idx v) , F₂ .idxf .sfunc (gi , val-idx u)} {val-idx v' , val-idx u'}
    (pair-idx {τ₀ = τ₀} s σ₁ σ₂ gi (val-idx v , val-idx u)) (map-idx M₁ , map-idx M₂)
  where
  gi = env-idx γ
  F× = fold-map τ₀ σr (σ₁ [×] σ₂) ⟦ s ⟧tm
  F₁ = fold-map τ₀ σr σ₁ ⟦ s ⟧tm
  F₂ = fold-map τ₀ σr σ₂ ⟦ s ⟧tm
map-idx {Γ} {γ} {τ₀} {σr} {s} (m-mu {τ' = τ'} {w = w} {w' = w'} M) =
  Ix.trans (μ τₛ) {Fμ .idxf .sfunc (gi , roll-mor τμ .idxf .sfunc (val-idx (≡-subst Val eμ w)))}
    {Fμ .idxf .sfunc (gi , roll-mor τμ .idxf .sfunc (Cμ .idxf .sfunc (val-idx w)))}
    {roll-mor τₛ .idxf .sfunc (val-idx (≡-subst Val eₛ w'))}
    (Fμ .idxf .sfunc-resp-≈ {gi , roll-mor τμ .idxf .sfunc (val-idx (≡-subst Val eμ w))}
      {gi , roll-mor τμ .idxf .sfunc (Cμ .idxf .sfunc (val-idx w))}
      (IxC.refl Γ {gi} ,
       roll-mor τμ .idxf .sfunc-resp-≈ {val-idx (≡-subst Val eμ w)} {Cμ .idxf .sfunc (val-idx w)} (val-idx-cast eμ w)))
    (Ix.trans (μ τₛ) {Fμ .idxf .sfunc (gi , roll-mor τμ .idxf .sfunc (Cμ .idxf .sfunc (val-idx w)))}
      {roll-mor τₛ .idxf .sfunc (Cₛ .idxf .sfunc (Fu .idxf .sfunc (gi , val-idx w)))}
      {roll-mor τₛ .idxf .sfunc (val-idx (≡-subst Val eₛ w'))}
      (idx-eq (fold-map-mu τ₀ σr τ' ⟦ s ⟧tm) (gi , val-idx w))
      (roll-mor τₛ .idxf .sfunc-resp-≈ {Cₛ .idxf .sfunc (Fu .idxf .sfunc (gi , val-idx w))} {val-idx (≡-subst Val eₛ w')}
        (Ix.trans (τₛ [ μ τₛ ]) {Cₛ .idxf .sfunc (Fu .idxf .sfunc (gi , val-idx w))} {Cₛ .idxf .sfunc (val-idx w')}
          {val-idx (≡-subst Val eₛ w')}
          (Cₛ .idxf .sfunc-resp-≈ {Fu .idxf .sfunc (gi , val-idx w)} {val-idx w'} (map-idx M))
          (Ix.sym (τₛ [ μ τₛ ]) {val-idx (≡-subst Val eₛ w')} {Cₛ .idxf .sfunc (val-idx w')} (val-idx-cast eₛ w')))))
  where
  gi = env-idx γ
  open MuShape τ₀ σr s τ'


private
  hd : ∀ n → 𝔽 (suc n) ⇒ SemiMod.𝕀
  hd n .SemiMod._⇒_.*→* .prop-setoid._⇒_.func o = o zero
  hd n .SemiMod._⇒_.*→* .prop-setoid._⇒_.func-resp-≈ e = e zero
  hd n .preserve-ze = ≈-refl
  hd n .preserve-+ = ≈-refl
  hd n .preserve-· = ≈-refl

  tl : ∀ n → 𝔽 (suc n) ⇒ 𝔽 n
  tl n .SemiMod._⇒_.*→* .prop-setoid._⇒_.func o k = o (suc k)
  tl n .SemiMod._⇒_.*→* .prop-setoid._⇒_.func-resp-≈ e k = e (suc k)
  tl n .preserve-ze k = ≈-refl
  tl n .preserve-+ k = ≈-refl
  tl n .preserve-· k = ≈-refl

val-fib : ∀ {τ} (fo : first-order τ) (v : Val τ) → 𝔽 (width v) ⇒ Fib τ (val-idx v)
val-fib unit           unit       = SemiMod.id (𝔽 1)
val-fib (base s)       (const a)  = SemiMod.id (𝔽 (sort-width s))
val-fib (fo₁ [+] fo₂)  (inl v)    = SemiMod.pair (hd (width v)) (val-fib fo₁ v SemiMod.∘ tl (width v))
val-fib (fo₁ [+] fo₂)  (inr v)    = SemiMod.pair (hd (width v)) (val-fib fo₂ v SemiMod.∘ tl (width v))
val-fib (fo₁ [×] fo₂)  (pair v u) =
  SemiMod.pair (hd (width v + width u))
    (SemiMod.pair (val-fib fo₁ v SemiMod.∘ mat (M.p₁ {width v} {width u}))
                  (val-fib fo₂ u SemiMod.∘ mat (M.p₂ {width v} {width u}))
     SemiMod.∘ tl (width v + width u))
val-fib (μ {τ = τ} fo) (roll v)   =
  roll-mor τ .famf .transf (val-idx v) SemiMod.∘ val-fib (fo-inst fo (μ fo)) v

env-fib : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) (γ : Env Γ) → 𝔽 (width-env γ) ⇒ FibC Γ (env-idx γ)
env-fib emp         emp     = SemiMod.ε-map (𝔽 0) _
env-fib (Γ-fo ▸ fo) (γ · v) =
  SemiMod.pair (env-fib Γ-fo γ SemiMod.∘ mat (M.p₁ {width-env γ} {width v}))
               (val-fib fo v SemiMod.∘ mat (M.p₂ {width-env γ} {width v}))

dep-rel-val : ∀ {τ} (fo : first-order τ) (v : Val τ) (o : ∣ 𝔽 (width v) ∣) →
              DepRel τ (val-rel fo v) o (val-fib fo v .func o)
dep-rel-val unit     unit      o k = ≈-refl
dep-rel-val (base s) (const a) o k = ≈-refl
dep-rel-val {τ₁ [+] τ₂} (fo₁ [+] fo₂) (inl v) o =
  ≈-sym (proj₁ e) ,
  DepRel-resp′ τ₁ (bound₁ ≤-refl) (ValRel-at-bound τ₁ (val-rel fo₁ v)) (λ k → ≈-refl) (Fib.sym τ₁ i (proj₂ e))
    (DepRel-at-bound τ₁ (val-rel fo₁ v) (dep-rel-val fo₁ v (λ k → o (suc k))))
  where
  i = val-idx v
  e = subst-refl ⟦ τ₁ [+] τ₂ ⟧ {inj₁ i} (Ix.refl (τ₁ [+] τ₂) {inj₁ i}) (val-fib (fo₁ [+] fo₂) (inl v) .func o)
dep-rel-val {τ₁ [+] τ₂} (fo₁ [+] fo₂) (inr v) o =
  ≈-sym (proj₁ e) ,
  DepRel-resp′ τ₂ (bound₂ ≤-refl) (ValRel-at-bound τ₂ (val-rel fo₂ v)) (λ k → ≈-refl) (Fib.sym τ₂ i (proj₂ e))
    (DepRel-at-bound τ₂ (val-rel fo₂ v) (dep-rel-val fo₂ v (λ k → o (suc k))))
  where
  i = val-idx v
  e = subst-refl ⟦ τ₁ [+] τ₂ ⟧ {inj₂ i} (Ix.refl (τ₁ [+] τ₂) {inj₂ i}) (val-fib (fo₁ [+] fo₂) (inr v) .func o)
dep-rel-val {τ₁ [×] τ₂} (fo₁ [×] fo₂) (pair v u) o =
  ≈-refl ,
  (DepRel-at-bound τ₁ (val-rel fo₁ v) (dep-rel-val fo₁ v (ap (M.p₁ {width v} {width u}) (λ k → o (suc k)))) ,
   DepRel-at-bound τ₂ (val-rel fo₂ u) (dep-rel-val fo₂ u (ap (M.p₂ {width v} {width u}) (λ k → o (suc k)))))
dep-rel-val {μ τ} (μ fo) (roll v) o =
  DepRel-transport⁻′ (τ [ μ τ ]) (bound-μ τ ≤-refl) (idx-eq (unroll-roll τ) i)
    (ValRel-at-bound (τ [ μ τ ]) (val-rel fo′ v))
    (fam-eq (unroll-roll τ) i (val-fib fo′ v .func o))
    (DepRel-at-bound (τ [ μ τ ]) (val-rel fo′ v) (dep-rel-val fo′ v o))
  where
  fo′ = fo-inst fo (μ fo)
  i = val-idx v

env-dep : ∀ {Γ} (Γ-fo : first-order-ctxt Γ) (γ : Env Γ) s (x : ∣ 𝔽 (width-env γ) ∣) →
          EnvDepRel (env-rel Γ-fo γ) s x (env-fib Γ-fo γ .func x)
env-dep emp         emp     s x = prop.tt
env-dep {Γ ▸ τ} (Γ-fo ▸ fo) (γ · v) s x =
  env-dep Γ-fo γ s (ap (M.p₁ {width-env γ} {width v}) x) ,
  (Fib.ε τ i , (Fib.+-lunit τ i ,
    DepRel-resp τ (val-rel fo v) (λ k → ≈-refl) (Fib.sym τ i (Fib.+-runit τ i))
      (dep-rel-val fo v (ap (M.p₂ {width-env γ} {width v}) x))))
  where i = val-idx v

dep-rel-unique : ∀ {τ} (fo : first-order τ) {v : Val τ} {i : Ix τ} (r : ValRel τ v i)
                 {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} → DepRel τ r o d →
                 Fib._≈_ τ (val-idx v) (val-fib fo v .func o) (⟦ τ ⟧ .fam .subst (val-rel-unique fo r) .func d)
dep-rel-unique unit     {unit}    {i} r     {o} {d} h k = ≈-trans (h k) (≈-sym (subst-refl ⟦ unit ⟧ {i} _ d k))
dep-rel-unique (base s) {const a} {i} ⟪ e ⟫ {o} {d} h k = ≈-trans (h k) (≈-sym (subst-base {s} {i} {a} e d k))
dep-rel-unique {τ₁ [+] τ₂} (fo₁ [+] fo₂) {inl v} {i} (i' , r , ⟪ e ⟫) {o} {d} (h₀ , h) =
  Fib.trans (τ₁ [+] τ₂) (inj₁ j)
    (h₀ , dep-rel-unique fo₁ (ValRel-at-bound τ₁ r) (DepRel-at-bound τ₁ r h))
    (Fib.sym (τ₁ [+] τ₂) (inj₁ j)
      (Fib.trans (τ₁ [+] τ₂) (inj₁ j) (subst-trans ⟦ τ₁ [+] τ₂ ⟧ {i} {inj₁ i'} {inj₁ j} e e₁ d)
                                     (subst-inj₁ {τ₁} {τ₂} {i'} {j} e₁ d₁)))
  where
  j  = val-idx v
  e₁ = val-rel-unique fo₁ (ValRel-at-bound τ₁ r)
  d₁ = ⟦ τ₁ [+] τ₂ ⟧ .fam .subst {i} {inj₁ i'} e .func d
dep-rel-unique {τ₁ [+] τ₂} (fo₁ [+] fo₂) {inr v} {i} (i' , r , ⟪ e ⟫) {o} {d} (h₀ , h) =
  Fib.trans (τ₁ [+] τ₂) (inj₂ j)
    (h₀ , dep-rel-unique fo₂ (ValRel-at-bound τ₂ r) (DepRel-at-bound τ₂ r h))
    (Fib.sym (τ₁ [+] τ₂) (inj₂ j)
      (Fib.trans (τ₁ [+] τ₂) (inj₂ j) (subst-trans ⟦ τ₁ [+] τ₂ ⟧ {i} {inj₂ i'} {inj₂ j} e e₁ d)
                                     (subst-inj₂ {τ₁} {τ₂} {i'} {j} e₁ d₁)))
  where
  j  = val-idx v
  e₁ = val-rel-unique fo₂ (ValRel-at-bound τ₂ r)
  d₁ = ⟦ τ₁ [+] τ₂ ⟧ .fam .subst {i} {inj₂ i'} e .func d
dep-rel-unique {τ₁ [×] τ₂} (fo₁ [×] fo₂) {pair v u} {i , j} (r , r') {o} {d} (h₀ , (h₁ , h₂)) =
  Fib.trans (τ₁ [×] τ₂) (val-idx v , val-idx u)
    (h₀ , (dep-rel-unique fo₁ (ValRel-at-bound τ₁ r) (DepRel-at-bound τ₁ r h₁) ,
           dep-rel-unique fo₂ (ValRel-at-bound τ₂ r') (DepRel-at-bound τ₂ r' h₂)))
    (Fib.sym (τ₁ [×] τ₂) (val-idx v , val-idx u)
      (subst-pair {τ₁} {τ₂} {i} {val-idx v} {j} {val-idx u}
        (val-rel-unique fo₁ (ValRel-at-bound τ₁ r)) (val-rel-unique fo₂ (ValRel-at-bound τ₂ r')) d))
dep-rel-unique {μ τ} (μ fo) {roll v} {i} r {o} {d} h =
  Fib.trans (μ τ) (roll-mor τ .idxf .sfunc j)
    (roll-mor τ .famf .transf j .func-resp-≈ (dep-rel-unique fo′ (ValRel-at-bound (τ [ μ τ ]) r) (DepRel-at-bound (τ [ μ τ ]) r h)))
    (Fib.trans (μ τ) (roll-mor τ .idxf .sfunc j)
      (transf-natural (roll-mor τ) {unroll-mor τ .idxf .sfunc i} {j} e₁ d₀)
      (Fib.trans (μ τ) (roll-mor τ .idxf .sfunc j)
        (⟦ μ τ ⟧ .fam .subst {i₀} {roll-mor τ .idxf .sfunc j} (roll-mor τ .idxf .sfunc-resp-≈ e₁) .func-resp-≈ roll-unroll-d)
        (Fib.sym (μ τ) (roll-mor τ .idxf .sfunc j)
          (subst-trans ⟦ μ τ ⟧ {i} {roll-mor τ .idxf .sfunc (unroll-mor τ .idxf .sfunc i)} {roll-mor τ .idxf .sfunc j}
            (Ix.sym (μ τ) {roll-mor τ .idxf .sfunc (unroll-mor τ .idxf .sfunc i)} {i} E)
            (roll-mor τ .idxf .sfunc-resp-≈ e₁) d))))
  where
  fo′ = fo-inst fo (μ fo)
  j   = val-idx v
  e₁  = val-rel-unique fo′ {v} {unroll-mor τ .idxf .sfunc i} (ValRel-at-bound (τ [ μ τ ]) r)
  d₀  = unroll-mor τ .famf .transf i .func d
  E   = idx-eq (roll-unroll τ) i
  i₀  = roll-mor τ .idxf .sfunc (unroll-mor τ .idxf .sfunc i)
  roll-unroll-d : Fib._≈_ (μ τ) i₀ (roll-mor τ .famf .transf (unroll-mor τ .idxf .sfunc i) .func d₀)
                                    (⟦ μ τ ⟧ .fam .subst {i} {i₀} (Ix.sym (μ τ) {i₀} {i} E) .func d)
  roll-unroll-d =
    Fib.trans (μ τ) i₀
      (Fib.sym (μ τ) i₀
        (Fib.trans (μ τ) i₀ (Fib.sym (μ τ) i₀ (subst-trans ⟦ μ τ ⟧ {i₀} {i} {i₀} E (Ix.sym (μ τ) {i₀} {i} E) _))
                            (subst-refl ⟦ μ τ ⟧ {i₀} (Ix.trans (μ τ) {i₀} {i} {i₀} E (Ix.sym (μ τ) {i₀} {i} E)) _)))
      (⟦ μ τ ⟧ .fam .subst {i} {i₀} (Ix.sym (μ τ) {i₀} {i} E) .func-resp-≈ (fam-eq (roll-unroll τ) i d))

soundness-dep : ∀ {Γ τ} (Γ-fo : first-order-ctxt Γ) (fo : first-order τ) →
                ∀ {t : Γ ⊢ τ} {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ]) (s : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣) →
                Fib._≈_ τ (val-idx v)
                  (val-fib fo v .func (ap R (inputs γ s x)))
                  (Fib._+_ τ (val-idx v) (ctrl-dep-at τ (val-idx v) s)
                    (⟦ τ ⟧ .fam .subst (soundness-val D) .func
                      (⟦ t ⟧tm .famf .transf (env-idx γ) .func (env-fib Γ-fo γ .func x))))
soundness-dep {τ = τ} Γ-fo fo {γ = γ} {v} D s x =
  Fib.trans τ (val-idx v)
    (dep-rel-unique fo (fundamental-val D rγ) (fundamental D rγ s x (env-fib Γ-fo γ .func x) (env-dep Γ-fo γ s x)))
    (subst-ctrl-dep+ τ (soundness-val D) s _)
  where rγ = env-rel Γ-fo γ

val-idx-inj : ∀ {τ} (fo : first-order τ) {v v' : Val τ} → Ix._≈_ τ (val-idx v) (val-idx v') → v ≈v v'
val-idx-inj unit          {unit}     {unit}       e = unit
val-idx-inj (base s)      {const a}  {const b}    e = const e
val-idx-inj (fo₁ [+] fo₂) {inl v}    {inl v'}     e = inl (val-idx-inj fo₁ e)
val-idx-inj (fo₁ [+] fo₂) {inl v}    {inr v'}     e = prop.⊥-elim e
val-idx-inj (fo₁ [+] fo₂) {inr v}    {inl v'}     e = prop.⊥-elim e
val-idx-inj (fo₁ [+] fo₂) {inr v}    {inr v'}     e = inr (val-idx-inj fo₂ e)
val-idx-inj (fo₁ [×] fo₂) {pair v u} {pair v' u'} (e₁ , e₂) = pair (val-idx-inj fo₁ e₁) (val-idx-inj fo₂ e₂)
val-idx-inj {μ τ} (μ fo)  {roll v}   {roll v'}    e =
  roll (val-idx-inj fo′ {v} {v'}
    (Ix.trans (τ [ μ τ ]) {i} {unroll-mor τ .idxf .sfunc (roll-mor τ .idxf .sfunc i)} {i'}
      (unroll-roll-idx τ i)
      (Ix.trans (τ [ μ τ ]) {unroll-mor τ .idxf .sfunc (roll-mor τ .idxf .sfunc i)}
                            {unroll-mor τ .idxf .sfunc (roll-mor τ .idxf .sfunc i')} {i'}
        (unroll-mor τ .idxf .sfunc-resp-≈ {roll-mor τ .idxf .sfunc i} {roll-mor τ .idxf .sfunc i'} e)
        (idx-eq (unroll-roll τ) i'))))
  where
  fo′ = fo-inst fo (μ fo)
  i   = val-idx v
  i'  = val-idx v'

adequacy : ∀ {Γ τ} (Γ-fo : first-order-ctxt Γ) (fo : first-order τ) {t : Γ ⊢ τ} {γ : Env Γ} {v : Val τ}
           {R : M.Matrix (width v) (suc (width-env γ))}
           (e : Ix._≈_ τ (⟦ t ⟧tm .idxf .sfunc (env-idx γ)) (val-idx v)) →
           (∀ (s : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣) →
             Fib._≈_ τ (val-idx v)
               (val-fib fo v .func (ap R (inputs γ s x)))
               (Fib._+_ τ (val-idx v) (ctrl-dep-at τ (val-idx v) s)
                 (⟦ τ ⟧ .fam .subst e .func (⟦ t ⟧tm .famf .transf (env-idx γ) .func (env-fib Γ-fo γ .func x))))) →
           ∀ {v' R'} (D : γ , t ⇓ v' [ R' ]) →
           (v ≈v v') ∧
           (∀ (s : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣) →
             Fib._≈_ τ (val-idx v')
               (⟦ τ ⟧ .fam .subst
                 (Ix.trans τ {val-idx v} {⟦ t ⟧tm .idxf .sfunc (env-idx γ)} {val-idx v'}
                   (Ix.sym τ {⟦ t ⟧tm .idxf .sfunc (env-idx γ)} {val-idx v} e) (soundness-val D))
                 .func (val-fib fo v .func (ap R (inputs γ s x))))
               (val-fib fo v' .func (ap R' (inputs γ s x))))
adequacy {τ = τ} Γ-fo fo {t} {γ} {v} {R} e h {v'} {R'} D =
  val-idx-inj fo E , λ s x →
    Fib.trans τ i' (⟦ τ ⟧ .fam .subst E .func-resp-≈ (h s x))
      (Fib.trans τ i' (subst-ctrl-dep+ τ E s _)
        (Fib.trans τ i'
          (Fib.+-cong τ i' (Fib.refl τ i') (Fib.sym τ i' (subst-trans ⟦ τ ⟧ e E (d x))))
          (Fib.sym τ i' (soundness-dep Γ-fo fo D s x))))
  where
  i   = val-idx v
  i'  = val-idx v'
  E   = Ix.trans τ {i} {⟦ t ⟧tm .idxf .sfunc (env-idx γ)} {i'} (Ix.sym τ {⟦ t ⟧tm .idxf .sfunc (env-idx γ)} {i} e) (soundness-val D)
  d   = λ x → ⟦ t ⟧tm .famf .transf (env-idx γ) .func (env-fib Γ-fo γ .func x)

open import interaction.graph S +-idem using (collapse)
open import interaction.dependence-graph Sig S ℐ ctrl-weight +-idem using (graph; agree)

agreement : ∀ {Γ τ} (Γ-fo : first-order-ctxt Γ) (fo : first-order τ) →
            ∀ {t : Γ ⊢ τ} {γ : Env Γ} {v R} (D : γ , t ⇓ v [ R ]) (s : Setoid.Carrier A) (x : ∣ 𝔽 (width-env γ) ∣) →
            Fib._≈_ τ (val-idx v)
              (val-fib fo v .func (ap (collapse (graph D)) (inputs γ s x)))
              (Fib._+_ τ (val-idx v) (ctrl-dep-at τ (val-idx v) s)
                (⟦ τ ⟧ .fam .subst (soundness-val D) .func
                  (⟦ t ⟧tm .famf .transf (env-idx γ) .func (env-fib Γ-fo γ .func x))))
agreement {τ = τ} Γ-fo fo {γ = γ} {v} D s x =
  Fib.trans τ (val-idx v)
    (val-fib fo v .func-resp-≈ (app-congₘ (agree D) (inputs γ s x)))
    (soundness-dep Γ-fo fo D s x)
