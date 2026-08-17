{-# OPTIONS --prop --postfix-projections --safe --inversion-max-depth=500 #-}

-- The interpretation of roll and fold, read against the relation at μ-types. A rolled value's
-- payload is compared, through the interpretation's map into the carrier, with the root shape of
-- the tree; a fold's action on a tree node is compared, through the interpretation's map out of
-- the carrier, with the operational map over the payload. Both maps are structural in the body,
-- so their action is computed at each type former; at a nested μ-type in the body they act
-- through the carriers' comparison maps, which are not read here, so the computations assume the
-- body has no μ-types.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _<_)
open import Data.Nat.Properties using (n<1+n)
open import Induction.WellFounded using (Acc; acc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality as ≡
import prop
open import prop using (_∧_; ∃; Prf; ⟪_⟫; _,_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
open import signature.interpretation using (Interpretation)
open import categories using (Category; HasProducts; HasCoproducts)
open import polynomial-functor using (Poly; extend)
import indexed-family
import ho-model
import language-interpretation

module ho-mu
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  (let module Sc = CommutativeSemiring S)
  (+-idem : ∀ x → Setoid._≈_ A (x Sc.+ x) x)
  (w-idem : Setoid._≈_ A (elim-weight Sc.· elim-weight) elim-weight)
  (w-absorb : ∀ x → Setoid._≈_ A ((elim-weight Sc.· x) Sc.+ elim-weight) elim-weight)
  where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ elim-weight

open import ho-relation S elim-weight Sig ℐ +-idem w-idem w-absorb

open model using (𝔽; mat; module Ls; module SemiMod)
open SemiMod using (Semimodule; _⇒_)
open Semimodule using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ using (func)
open FD using (Obj; Mor; idx; fam; fm; idxf; famf; Constant; mkSort)
open indexed-family.Fam using (subst)
open indexed-family._⇒f_ using (transf)
open prop-setoid._⇒_ using () renaming (func to sfunc)
open LI using (⟦_⟧ty; ⟦_⟧tm; elim-const; ty-unit)
open Constant using (at)
open Sc using (ι; ε) renaming (_≈_ to _≈s_; _+_ to _+ₛ_; _·_ to _·ₛ_)
open Setoid A using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open Sc using (+-cong; ·-cong; +-lunit; +-comm; +-assoc; ·-lunit; ·-comm)

module FDC = Category FD.cat
open HasCoproducts FD.coproducts using (coprod)
module FDP = HasProducts FD.products

-- Types whose bodies contain no μ-types.
μ-free-ty : ∀ {Δ} → type Δ → Set
μ-free-ty (var i)   = ⊤
μ-free-ty unit      = ⊤
μ-free-ty (base s)  = ⊤
μ-free-ty (σ [+] τ) = μ-free-ty σ × μ-free-ty τ
μ-free-ty (σ [×] τ) = μ-free-ty σ × μ-free-ty τ
μ-free-ty (σ [→] τ) = ⊤
μ-free-ty (μ τ)     = ⊥

-- Equations between objects act on indices and fibres as transports; at a coproduct of lifted
-- summands or a lifted product they act on the components.
≡→≈ : ∀ (X : Obj) {x y : Setoid.Carrier (X .idx)} → x ≡ y → Setoid._≈_ (X .idx) x y
≡→≈ X {x} refl = Setoid.refl (X .idx) {x}

subst-≡ : ∀ (X : Obj) {x y : Setoid.Carrier (X .idx)} (e : x ≡ y) (d : ∣ X .fam .fm x ∣) →
          Semimodule._≈_ (X .fam .fm y) (X .fam .subst (≡→≈ X e) .func d) (≡.subst (λ z → ∣ X .fam .fm z ∣) e d)
subst-≡ X {x} refl d = X .fam .indexed-family.Fam.refl* {x} .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (Semimodule.refl (X .fam .fm x) {d})

coprodL : Obj → Obj → Obj
coprodL X Y = coprod (FD.Lf X) (FD.Lf Y)

prodL : Obj → Obj → Obj
prodL X Y = FD.Lf (FDP.prod X Y)

≡-to-⇒-inl : ∀ {X X' Y Y' : Obj} (p : X ≡ X') (q : Y ≡ Y') (x : Setoid.Carrier (X .idx)) →
             FDC.≡-to-⇒ (≡.cong₂ coprodL p q) .idxf .sfunc (inj₁ x) ≡ inj₁ (FDC.≡-to-⇒ p .idxf .sfunc x)
≡-to-⇒-inl refl refl x = refl

≡-to-⇒-inr : ∀ {X X' Y Y' : Obj} (p : X ≡ X') (q : Y ≡ Y') (y : Setoid.Carrier (Y .idx)) →
             FDC.≡-to-⇒ (≡.cong₂ coprodL p q) .idxf .sfunc (inj₂ y) ≡ inj₂ (FDC.≡-to-⇒ q .idxf .sfunc y)
≡-to-⇒-inr refl refl y = refl

≡-to-⇒-pair : ∀ {X X' Y Y' : Obj} (p : X ≡ X') (q : Y ≡ Y') (x : Setoid.Carrier (X .idx)) (y : Setoid.Carrier (Y .idx)) →
              FDC.≡-to-⇒ (≡.cong₂ prodL p q) .idxf .sfunc (x , y) ≡ (FDC.≡-to-⇒ p .idxf .sfunc x , FDC.≡-to-⇒ q .idxf .sfunc y)
≡-to-⇒-pair refl refl x y = refl

≡-to-⇒-inl-fam : ∀ {X X' Y Y' : Obj} (p : X ≡ X') (q : Y ≡ Y') (x : Setoid.Carrier (X .idx))
                 (d : ∣ coprodL X Y .fam .fm (inj₁ x) ∣) →
                 Semimodule._≈_ (coprodL X' Y' .fam .fm (inj₁ (FDC.≡-to-⇒ p .idxf .sfunc x)))
                   (coprodL X' Y' .fam .subst {FDC.≡-to-⇒ (≡.cong₂ coprodL p q) .idxf .sfunc (inj₁ x)}
                      {inj₁ (FDC.≡-to-⇒ p .idxf .sfunc x)} (≡→≈ (coprodL X' Y') (≡-to-⇒-inl p q x)) .func
                      (FDC.≡-to-⇒ (≡.cong₂ coprodL p q) .famf .transf (inj₁ x) .func d))
                   (proj₁ d , FDC.≡-to-⇒ p .famf .transf x .func (proj₂ d))
≡-to-⇒-inl-fam {X} {.X} {Y} {.Y} refl refl x d = subst-≡ (coprodL X Y) {inj₁ x} refl d

≡-to-⇒-inr-fam : ∀ {X X' Y Y' : Obj} (p : X ≡ X') (q : Y ≡ Y') (y : Setoid.Carrier (Y .idx))
                 (d : ∣ coprodL X Y .fam .fm (inj₂ y) ∣) →
                 Semimodule._≈_ (coprodL X' Y' .fam .fm (inj₂ (FDC.≡-to-⇒ q .idxf .sfunc y)))
                   (coprodL X' Y' .fam .subst {FDC.≡-to-⇒ (≡.cong₂ coprodL p q) .idxf .sfunc (inj₂ y)}
                      {inj₂ (FDC.≡-to-⇒ q .idxf .sfunc y)} (≡→≈ (coprodL X' Y') (≡-to-⇒-inr p q y)) .func
                      (FDC.≡-to-⇒ (≡.cong₂ coprodL p q) .famf .transf (inj₂ y) .func d))
                   (proj₁ d , FDC.≡-to-⇒ q .famf .transf y .func (proj₂ d))
≡-to-⇒-inr-fam {X} {.X} {Y} {.Y} refl refl y d = subst-≡ (coprodL X Y) {inj₂ y} refl d

≡-to-⇒-pair-fam : ∀ {X X' Y Y' : Obj} (p : X ≡ X') (q : Y ≡ Y') (x : Setoid.Carrier (X .idx)) (y : Setoid.Carrier (Y .idx))
                  (d : ∣ prodL X Y .fam .fm (x , y) ∣) →
                  Semimodule._≈_ (prodL X' Y' .fam .fm (FDC.≡-to-⇒ p .idxf .sfunc x , FDC.≡-to-⇒ q .idxf .sfunc y))
                    (prodL X' Y' .fam .subst {FDC.≡-to-⇒ (≡.cong₂ prodL p q) .idxf .sfunc (x , y)}
                       {FDC.≡-to-⇒ p .idxf .sfunc x , FDC.≡-to-⇒ q .idxf .sfunc y} (≡→≈ (prodL X' Y') (≡-to-⇒-pair p q x y)) .func
                       (FDC.≡-to-⇒ (≡.cong₂ prodL p q) .famf .transf (x , y) .func d))
                    (proj₁ d , (FDC.≡-to-⇒ p .famf .transf x .func (proj₁ (proj₂ d)) ,
                                FDC.≡-to-⇒ q .famf .transf y .func (proj₂ (proj₂ d))))
≡-to-⇒-pair-fam {X} {.X} {Y} {.Y} refl refl x y d = subst-≡ (prodL X Y) {x , y} refl d

-- The comparison of a rolled value's payload with the tree's root shape: the interpretation's map
-- from the unfolded type into the carrier, at each type σ' of the body's subterms, followed by the
-- carrier's embedding and reindexing of shapes.
module Roll (τ : type 1) where
  P : Poly FD.cat 1
  P = LI.as-poly τ (λ ())

  δ∅ : Fin 0 → Obj
  δ∅ = interp.δ∅𝒟

  δ' : Fin 1 → Obj
  δ' = extend δ∅ (FD.μ-fam P δ∅)

  Q : type 1 → Poly FD.cat 1
  Q σ' = LI.as-poly σ' (λ ())

  Φ : (σ' : type 1) → Mor ⟦ σ' [ μ τ ] ⟧ (FD.fobj FD.μ-fam (Q σ') δ')
  Φ σ' = LI.sub-as-apply-fwd σ' (μ τ)

  mor₀ = FD.InMapDef.mor₀ P δ∅

  toShape : (σ' : type 1) → Ix (σ' [ μ τ ]) → Shape δ∅ FD.∣ Q σ' ∣ (η₀ τ)
  toShape σ' i = FD.Reindex.reindex-shape δ' δ∅ FD.∣ Q σ' ∣ mor₀ (FD.InMapDef.embed-idx P δ∅ (Q σ') (Φ σ' .idxf .sfunc i))

  toFib : (σ' : type 1) (i : Ix (σ' [ μ τ ])) → ∣ Fib (σ' [ μ τ ]) i ∣ → ∣ FibSh δ∅ (Q σ') (d₀ τ) (toShape σ' i) ∣
  toFib σ' i d =
    FD.Reindex.reindex-fam δ' δ∅ (Q σ') mor₀ .func
      (FD.InMapDef.embed-fam P δ∅ (Q σ') (Φ σ' .idxf .sfunc i) .func (Φ σ' .famf .transf i .func d))

  -- The interpretation of roll is this comparison at the body, under a node.
  roll-idx : ∀ (i : Ix (τ [ μ τ ])) →
             FD.InMapDef.inMor P δ∅ .idxf .sfunc (Φ τ .idxf .sfunc i) ≡ FD.Srt.Tree.sup (toShape τ i)
  roll-idx i = refl

  roll-fam : ∀ (i : Ix (τ [ μ τ ])) (d : ∣ Fib (τ [ μ τ ]) i ∣) →
             FD.InMapDef.inMor P δ∅ .famf .transf (Φ τ .idxf .sfunc i) .func (Φ τ .famf .transf i .func d) ≡ toFib τ i d
  roll-fam i d = refl

  -- The comparison respects the index setoid and is natural.
  toShape-resp : ∀ σ' {i i'} → Setoid._≈_ (⟦ σ' [ μ τ ] ⟧ .idx) i i' →
                 Tr.shape≈ δ∅ FD.∣ Q σ' ∣ (η₀ τ) (toShape σ' i) (toShape σ' i')
  toShape-resp σ' e =
    FD.Reindex.reindex-shape-resp δ' δ∅ FD.∣ Q σ' ∣ mor₀
      (FD.InMapDef.embed-idx-resp P δ∅ (Q σ') (Φ σ' .idxf .prop-setoid._⇒_.func-resp-≈ e))

  toFib-natural : ∀ σ' {i i'} (e : Setoid._≈_ (⟦ σ' [ μ τ ] ⟧ .idx) i i') d →
                  Semimodule._≈_ (FibSh δ∅ (Q σ') (d₀ τ) (toShape σ' i'))
                    (Tr.fib-shape-subst δ∅ (Q σ') (d₀ τ) {toShape σ' i} {toShape σ' i'} (toShape-resp σ' e) .func (toFib σ' i d))
                    (toFib σ' i' (⟦ σ' [ μ τ ] ⟧ .fam .subst e .func d))
  toFib-natural σ' {i} {i'} e d =
    Semimodule.trans X'
      (Semimodule.sym X'
        (FD.Reindex.reindex-fam-natural δ' δ∅ (Q σ') mor₀ {a} {a'} ea .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq
           (Semimodule.refl (TX.fib-shape (Q σ') (λ v → lift tt) a) {y})))
      (FD.Reindex.reindex-fam δ' δ∅ (Q σ') mor₀ .SemiMod._⇒_.func-resp-≈
        (Semimodule.trans (TX.fib-shape (Q σ') (λ v → lift tt) a')
          (Semimodule.sym (TX.fib-shape (Q σ') (λ v → lift tt) a')
            (FD.InMapDef.embed-fam-natural P δ∅ (Q σ') {z} {z'} ez .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq
               (Semimodule.refl (FD.fobj FD.μ-fam (Q σ') δ' .fam .fm z) {Φ σ' .famf .transf i .func d})))
          (FD.InMapDef.embed-fam P δ∅ (Q σ') z' .SemiMod._⇒_.func-resp-≈
            (Semimodule.sym (FD.fobj FD.μ-fam (Q σ') δ' .fam .fm z')
              (Φ σ' .famf .indexed-family._⇒f_.natural e .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq
                 (Semimodule.refl (Fib (σ' [ μ τ ]) i) {d}))))))
    where
    module TX = Tr δ'
    z = Φ σ' .idxf .sfunc i
    z' = Φ σ' .idxf .sfunc i'
    ez = Φ σ' .idxf .prop-setoid._⇒_.func-resp-≈ e
    a = FD.InMapDef.embed-idx P δ∅ (Q σ') z
    a' = FD.InMapDef.embed-idx P δ∅ (Q σ') z'
    ea = FD.InMapDef.embed-idx-resp P δ∅ (Q σ') ez
    y = FD.InMapDef.embed-fam P δ∅ (Q σ') z .func (Φ σ' .famf .transf i .func d)
    X' = FibSh δ∅ (Q σ') (d₀ τ) (toShape σ' i')

  -- The comparison is linear.
  toFib-+ : ∀ σ' i d d' → Semimodule._≈_ (FibSh δ∅ (Q σ') (d₀ τ) (toShape σ' i))
                            (toFib σ' i (Semimodule._+_ (Fib (σ' [ μ τ ]) i) d d'))
                            (Semimodule._+_ (FibSh δ∅ (Q σ') (d₀ τ) (toShape σ' i)) (toFib σ' i d) (toFib σ' i d'))
  toFib-+ σ' i d d' =
    Semimodule.trans X (R .SemiMod._⇒_.func-resp-≈ (Semimodule.trans Y (E .SemiMod._⇒_.func-resp-≈ (Φ σ' .famf .transf i .SemiMod._⇒_.preserve-+ {d} {d'}))
                                                                      (E .SemiMod._⇒_.preserve-+)))
                       (R .SemiMod._⇒_.preserve-+)
    where
    X = FibSh δ∅ (Q σ') (d₀ τ) (toShape σ' i)
    R = FD.Reindex.reindex-fam δ' δ∅ (Q σ') mor₀ {a = FD.InMapDef.embed-idx P δ∅ (Q σ') (Φ σ' .idxf .sfunc i)}
    E = FD.InMapDef.embed-fam P δ∅ (Q σ') (Φ σ' .idxf .sfunc i)
    Y = Tr.fib-shape δ' (Q σ') (λ v → lift tt) (FD.InMapDef.embed-idx P δ∅ (Q σ') (Φ σ' .idxf .sfunc i))

  -- The comparison at each type former.
  ≡→sh : ∀ σ' {x y} → x ≡ y → Tr.shape≈ δ∅ FD.∣ Q σ' ∣ (η₀ τ) x y
  ≡→sh σ' {x} refl = Tr.shape≈-refl δ∅ FD.∣ Q σ' ∣ (η₀ τ) x

  toShape-inl : ∀ σ₁ σ₂ i → toShape (σ₁ [+] σ₂) (inj₁ i) ≡ inj₁ (toShape σ₁ i)
  toShape-inl σ₁ σ₂ i =
    ≡.cong (λ z → FD.Reindex.reindex-shape δ' δ∅ FD.∣ Q (σ₁ [+] σ₂) ∣ mor₀
                    (FD.InMapDef.embed-idx P δ∅ (Q (σ₁ [+] σ₂)) (LI.apply-fwd {0} {1} (σ₁ [+] σ₂) (λ ()) δ' .idxf .sfunc z)))
           (≡-to-⇒-inl (LI.ty-cong σ₁ (LI.push-pw (μ τ))) (LI.ty-cong σ₂ (LI.push-pw (μ τ)))
                       (LI.subst-fwd (push (μ τ)) σ₁ (λ ()) .idxf .sfunc i))

  toShape-inr : ∀ σ₁ σ₂ i → toShape (σ₁ [+] σ₂) (inj₂ i) ≡ inj₂ (toShape σ₂ i)
  toShape-inr σ₁ σ₂ i =
    ≡.cong (λ z → FD.Reindex.reindex-shape δ' δ∅ FD.∣ Q (σ₁ [+] σ₂) ∣ mor₀
                    (FD.InMapDef.embed-idx P δ∅ (Q (σ₁ [+] σ₂)) (LI.apply-fwd {0} {1} (σ₁ [+] σ₂) (λ ()) δ' .idxf .sfunc z)))
           (≡-to-⇒-inr (LI.ty-cong σ₁ (LI.push-pw (μ τ))) (LI.ty-cong σ₂ (LI.push-pw (μ τ)))
                       (LI.subst-fwd (push (μ τ)) σ₂ (λ ()) .idxf .sfunc i))

  toShape-pair : ∀ σ₁ σ₂ i j → toShape (σ₁ [×] σ₂) (i , j) ≡ (toShape σ₁ i , toShape σ₂ j)
  toShape-pair σ₁ σ₂ i j =
    ≡.cong (λ z → FD.Reindex.reindex-shape δ' δ∅ FD.∣ Q (σ₁ [×] σ₂) ∣ mor₀
                    (FD.InMapDef.embed-idx P δ∅ (Q (σ₁ [×] σ₂)) (LI.apply-fwd {0} {1} (σ₁ [×] σ₂) (λ ()) δ' .idxf .sfunc z)))
           (≡-to-⇒-pair (LI.ty-cong σ₁ (LI.push-pw (μ τ))) (LI.ty-cong σ₂ (LI.push-pw (μ τ)))
                        (LI.subst-fwd (push (μ τ)) σ₁ (λ ()) .idxf .sfunc i) (LI.subst-fwd (push (μ τ)) σ₂ (λ ()) .idxf .sfunc j))

  -- The value relation at the unfolded type is the shape relation at the body, over the relation at
  -- the μ-type at the recursive variable.
  roll-val : ∀ σ' → μ-free-ty σ' → ∀ N (a : Acc _<_ N) {v : Val (σ' [ μ τ ])} (p : size v < N) {i : Ix (σ' [ μ τ ])} →
             ValRel (σ' [ μ τ ]) v i →
             ShapeRel {Δ = 0} δ∅ (λ ()) σ' (push (μ τ)) (η₀ τ) N a (mu-VarRel (MuRel τ N a)) (no-ConstRel {n = 1}) v p (toShape σ' i)
  roll-val (var zero) _ N a p r = MuRel-of τ N a p r
  roll-val unit _ N a {unit} p r = tt
  roll-val (base b) _ N a {const c} p r = r
  roll-val (σ₁ [+] σ₂) (m₁ , m₂) N a {inl v} p {i} (i' , r , ⟪ e ⟫) =
    toShape σ₁ i' , roll-val σ₁ m₁ N a _ r ,
    ⟪ Tr.shape≈-trans δ∅ FD.∣ Q (σ₁ [+] σ₂) ∣ (η₀ τ) {toShape (σ₁ [+] σ₂) i} {toShape (σ₁ [+] σ₂) (inj₁ i')} {inj₁ (toShape σ₁ i')}
        (toShape-resp (σ₁ [+] σ₂) {i} {inj₁ i'} e) (≡→sh (σ₁ [+] σ₂) (toShape-inl σ₁ σ₂ i')) ⟫
  roll-val (σ₁ [+] σ₂) (m₁ , m₂) N a {inr v} p {i} (i' , r , ⟪ e ⟫) =
    toShape σ₂ i' , roll-val σ₂ m₂ N a _ r ,
    ⟪ Tr.shape≈-trans δ∅ FD.∣ Q (σ₁ [+] σ₂) ∣ (η₀ τ) {toShape (σ₁ [+] σ₂) i} {toShape (σ₁ [+] σ₂) (inj₂ i')} {inj₂ (toShape σ₂ i')}
        (toShape-resp (σ₁ [+] σ₂) {i} {inj₂ i'} e) (≡→sh (σ₁ [+] σ₂) (toShape-inr σ₁ σ₂ i')) ⟫
  roll-val (σ₁ [×] σ₂) (m₁ , m₂) N a {pair v u} p {i , j} (r , r') =
    ≡.subst (λ z → ShapeRel {Δ = 0} δ∅ (λ ()) (σ₁ [×] σ₂) (push (μ τ)) (η₀ τ) N a (mu-VarRel (MuRel τ N a)) (no-ConstRel {n = 1}) (pair v u) p z)
      (≡.sym (toShape-pair σ₁ σ₂ i j)) (roll-val σ₁ m₁ N a _ r , roll-val σ₂ m₂ N a _ r')
  roll-val (σ₁ [→] σ₂) _ N a p r = r
