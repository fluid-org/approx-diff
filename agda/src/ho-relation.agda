{-# OPTIONS --prop --postfix-projections --safe #-}

-- Agreement between the operational relation and the higher-order model, on the fragment without
-- μ-types, as a logical relation. A value is related to an index of its type's
-- interpretation by recursion on the type, behaviourally at arrow types: for related arguments and
-- any derivation of the body, the result is related. Over that, a dependence vector on the value's
-- positions is related to an element of the fibre: at first-order types position by position, at
-- arrow types the root exactly and the payload through application, comparing, for any added
-- source weight, the body's dependence through the root and that weight as source and the cells
-- and the argument as environment with the elimination constant at that source plus the
-- evaluation of the payload and the index's fibre map at the argument. Inputs are a source
-- weight and an environment vector, and the environment relation lets a cell carry further control
-- dependence below the elimination constant at the source in the additive order, which is how the
-- operational semantics attaches control dependence to values inside a branch where the
-- interpretation attaches it to the branch's result once. The fundamental lemma, by induction on
-- the term over all derivations, says the relation applied to the inputs is related to the term's
-- fibre map at the environment's denotation plus the elimination constant at the source. That the
-- constant absorbs such dependence needs the elimination weight to be idempotent and to absorb its
-- multiples under addition, and addition to be idempotent, as in a lattice.
open import Level using (0ℓ; lift)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; <-trans; n<1+n; m≤m+n; m≤n+m)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import every using (Every)
open import Data.List using ([]; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality as ≡
open import polynomial-functor using (Poly; extend)
import prop
open import prop using (_∧_; ∃; ∃ₛ; Prf; ⟪_⟫; _,_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import signature using (Signature)
import signature
open import signature.interpretation using (Interpretation; sort-vals-setoid)
open import categories using (Category; HasProducts; HasTerminal; HasWeakExponentials; HasStrongCoproducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
import indexed-family
open import indexed-family using (HasSetoidProducts)
import matrix
import semimodule
import commutative-monoid
import ho-model
import language-interpretation

module ho-relation
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) (elim-weight : Setoid.Carrier A)
  (Sig : Signature 0ℓ) (ℐ : Interpretation S Sig)
  (let module Sc = CommutativeSemiring S)
  -- Addition is idempotent, and the elimination weight is idempotent and absorbs its multiples.
  (+-idem : ∀ x → Setoid._≈_ A (x Sc.+ x) x)
  (w-idem : Setoid._≈_ A (elim-weight Sc.· elim-weight) elim-weight)
  (w-absorb : ∀ x → Setoid._≈_ A ((elim-weight Sc.· x) Sc.+ elim-weight) elim-weight)
  where

open Signature Sig
open Interpretation ℐ
open import language-syntax Sig renaming (_,_ to _▸_)
open import language-operational.evaluation Sig S ℐ elim-weight
open import language-operational.type-substitution Sig using (unfold-sub)

module model = ho-model S elim-weight
module interp = model.interp Sig ℐ
open model using (𝔽; mat; ι1-fwd; ι1-bwd; module Ls; module SemiMod)
open SemiMod using (Semimodule; _⇒_)
open Semimodule using () renaming (Carrier to ∣_∣)
open SemiMod._⇒_ using (func)

module M = matrix.Mat S
module SMP = HasProducts SemiMod.products
module FD = model.Fam⟨𝒟⟩μ
module SP = HasSetoidProducts model.SPmod

open FD using (Obj; Mor; idx; fam; fm; idxf; famf; Constant; mkSort)
open indexed-family.Fam using (subst)
open indexed-family._⇒f_ using (transf)
open prop-setoid._⇒_ using () renaming (func to sfunc)

-- The interpretation, at the parameters the higher-order model fixes.
module LI = language-interpretation Sig 0ℓ 0ℓ
  SemiMod.terminal SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀 model.SemiModExp
  interp.δ∅𝒟 interp.𝒟𝟙ty interp.𝒟unit-pt interp.𝒟-Sig-model model.elim-weight-endo
  (λ {X} {Y} → model.exp-const {X} {Y}) interp.𝒟𝟙ty-const interp.𝒟-sort-const

open LI using (⟦_⟧ty; ⟦_⟧ctxt; ⟦_⟧tm; ⟦_⟧tms; elim-const; ty-unit)
open Constant using (at)

module IP = model.FP.interp-primitives Sig ℐ
module FCμ = model.Fam⟨𝒞⟩μ

⟦_⟧ : type 0 → Obj
⟦ τ ⟧ = ⟦ τ ⟧ty (λ ())

Ix : type 0 → Set
Ix τ = Setoid.Carrier (⟦ τ ⟧ .idx)

Fib : (τ : type 0) → Ix τ → Semimodule
Fib τ i = ⟦ τ ⟧ .fam .fm i

IxC : ctxt → Set
IxC Γ = Setoid.Carrier (⟦ Γ ⟧ctxt .idx)

FibC : (Γ : ctxt) → IxC Γ → Semimodule
FibC Γ i = ⟦ Γ ⟧ctxt .fam .fm i

_≈A_ : Setoid.Carrier A → Setoid.Carrier A → Prop
_≈A_ = Setoid._≈_ A


-- The μ-carriers' trees over a parameter environment: shapes of the index-erased polynomials at a
-- sort environment, and the fibre at a shape under a decoration.
module Tr {m} (δₘ : Fin m → Obj) = FD.Tree δₘ

Shape : ∀ {m} (δₘ : Fin m → Obj) {n} → FD.Srt.Poly n → (Fin n → Fin m ⊎ FD.Sort m) → Set
Shape δₘ = Tr.⟦_⟧shape δₘ

El : ∀ {m} (δₘ : Fin m → Obj) → Fin m ⊎ FD.Sort m → Set
El δₘ = Tr.El δₘ

DecoAssign : ∀ {m} (δₘ : Fin m → Obj) → Fin m ⊎ FD.Sort m → Set _
DecoAssign δₘ = Tr.DecoAssign δₘ

FibSh : ∀ {m} (δₘ : Fin m → Obj) {n} (Q : Poly FD.cat n) {η : Fin n → Fin m ⊎ FD.Sort m}
        (d : ∀ j → DecoAssign δₘ (η j)) → Shape δₘ FD.∣ Q ∣ η → Semimodule
FibSh δₘ Q d x = Tr.fib-shape δₘ Q d x

FibEl : ∀ {m} (δₘ : Fin m → Obj) (r : Fin m ⊎ FD.Sort m) → DecoAssign δₘ r → El δₘ r → Semimodule
FibEl δₘ r d x = Tr.fib-el δₘ r d x

-- The polynomial of a variable: a variable of the polynomial or a constant from the environment.
Var : ∀ {Δ n} → (Fin Δ → Obj) → Fin n ⊎ Fin Δ → Poly FD.cat n
Var δ = [ Poly.var , (λ j → Poly.const (δ j)) ]

-- The relations at the variables of an open type under a substitution of closed types: at the
-- polynomial's variables, values below a size bound against elements of the sort environment; at
-- the environment's, values against indices of the object there.
record VarRel {Δ n m} (δₘ : Fin m → Obj) (σ : TySub (n + Δ) 0) (η : Fin n → Fin m ⊎ FD.Sort m) (N : ℕ) : Set₁ where
  field rel : ∀ j (u : Val (σ (j ↑ˡ Δ))) → size u < N → El δₘ (η j) → Set

record ConstRel {Δ n} (δ : Fin Δ → Obj) (σ : TySub (n + Δ) 0) : Set₁ where
  field crel : ∀ k (u : Val (σ (n ↑ʳ k))) → Setoid.Carrier (δ k .idx) → Set

open VarRel public
open ConstRel public

extend-VarRel : ∀ {Δ n m} {δₘ : Fin m → Obj} {σ : TySub (n + Δ) 0} {η : Fin n → Fin m ⊎ FD.Sort m} {N}
                {ρ : type 0} {s : Fin m ⊎ FD.Sort m} →
                ((u : Val ρ) → size u < N → El δₘ s → Set) → VarRel δₘ σ η N →
                VarRel δₘ (extend σ ρ) (extend η s) N
extend-VarRel R₀ R .rel zero    = R₀
extend-VarRel R₀ R .rel (suc j) = R .rel j

lower-VarRel : ∀ {Δ n m} {δₘ : Fin m → Obj} {σ : TySub (n + Δ) 0} {η : Fin n → Fin m ⊎ FD.Sort m} {N N'} → N' < N →
               VarRel δₘ σ η N → VarRel δₘ σ η N'
lower-VarRel p R .rel j u q = R .rel j u (<-trans q p)

-- The environment's relations are unchanged by an extension of the polynomial's variables.
extend-ConstRel : ∀ {Δ n} {δ : Fin Δ → Obj} {σ : TySub (n + Δ) 0} {ρ : type 0} →
                  ConstRel δ σ → ConstRel δ (extend σ ρ)
extend-ConstRel R .crel = R .crel

no-ConstRel : ∀ {n} {σ : TySub (n + 0) 0} → ConstRel {Δ = 0} {n = n} (λ ()) σ
no-ConstRel .crel ()

-- The environment of the body of a closed μ-type: its own sort at the recursive variable.
η₀ : (τ : type 1) → Fin 1 → Fin 0 ⊎ FD.Sort 0
η₀ τ = extend (λ i → inj₁ i) (inj₂ (mkSort FD.∣ LI.as-poly τ (λ ()) ∣ (λ i → inj₁ i)))

mu-VarRel : ∀ {τ N} → ((u : Val (μ τ)) → size u < N → Ix (μ τ) → Set) →
            VarRel interp.δ∅𝒟 (push (μ τ)) (η₀ τ) N
mu-VarRel R .rel zero = R
mu-VarRel R .rel (suc ())

-- The relation at a variable, dispatched on its side of the environment.
var-rel : ∀ {Δ n m} (δₘ : Fin m → Obj) (δ : Fin Δ → Obj) (i : Fin (n + Δ)) (σ : TySub (n + Δ) 0)
          (η : Fin n → Fin m ⊎ FD.Sort m) (N : ℕ) → VarRel δₘ σ η N → ConstRel δ σ →
          (v : Val (σ i)) → size v < N → (s : Fin n ⊎ Fin Δ) → splitAt n i ≡ s →
          Shape δₘ FD.∣ Var δ s ∣ η → Set
var-rel δₘ δ i σ η N RP RΔ v p (inj₁ j) eq x =
  RP .rel j (≡.subst Val (≡.sym (≡.cong σ (splitAt⁻¹-↑ˡ eq))) v) (≡.subst (_< N) (≡.sym (size-subst _ v)) p) x
var-rel δₘ δ i σ η N RP RΔ v p (inj₂ k) eq x =
  RΔ .crel k (≡.subst Val (≡.sym (≡.cong σ (splitAt⁻¹-↑ʳ eq))) v) x

-- Values related to indices, by recursion on the type. A closure is related to a fibre map of the
-- exponential when, for every related argument and every derivation of the body at it, the result
-- is related to the map's index at the argument. A value of a μ-type is related to a tree when its
-- payload is related to the root shape over the body's environment, by well-founded recursion on
-- the value: the relation itself, at smaller values, stands at the recursive variable. A value at
-- an open type under a substitution of closed types is related to a shape of the type's polynomial
-- over a sort environment, given the relations at the variables; a nested μ-type extends the
-- substitution by its unfolding and the sort environment by its own sort.
ValRel : ∀ τ → Val τ → Ix τ → Set
MuRel : ∀ (τ : type 1) (N : ℕ) → Acc _<_ N → (v : Val (μ τ)) → size v < N → Ix (μ τ) → Set
ShapeRel : ∀ {Δ n m} (δₘ : Fin m → Obj) (δ : Fin Δ → Obj) (τ : type (n + Δ)) (σ : TySub (n + Δ) 0)
           (η : Fin n → Fin m ⊎ FD.Sort m) (N : ℕ) → Acc _<_ N → VarRel δₘ σ η N → ConstRel δ σ →
           (v : Val (sub σ τ)) → size v < N → Shape δₘ FD.∣ LI.as-poly τ δ ∣ η → Set

ValRel unit unit i = ⊤
ValRel (base s) (const c) i = Prf (Setoid._≈_ (sort-index s) i c)
ValRel (σ [+] τ) (inl v) i = Σ (Ix σ) λ i' → ValRel σ v i' × Prf (Setoid._≈_ (⟦ σ [+] τ ⟧ .idx) i (inj₁ i'))
ValRel (σ [+] τ) (inr v) i = Σ (Ix τ) λ i' → ValRel τ v i' × Prf (Setoid._≈_ (⟦ σ [+] τ ⟧ .idx) i (inj₂ i'))
ValRel (σ [×] τ) (pair v u) (i , j) = ValRel σ v i × ValRel τ u j
ValRel (σ [→] τ) (clo γ' t) f =
  ∀ {v : Val σ} {j : Ix σ} → ValRel σ v j → ∀ {u U} → γ' · v , t ⇓ u [ U ] → ValRel τ u (f .idxf .sfunc j)
ValRel (μ τ) v i = MuRel τ (suc (size v)) (<-wellFounded _) v (n<1+n _) i

MuRel τ N (acc rs) (roll w) p (Tr.sup x) =
  ShapeRel interp.δ∅𝒟 (λ ()) τ (push (μ τ)) (η₀ τ) (suc (size w)) (rs p)
    (mu-VarRel (MuRel τ (suc (size w)) (rs p))) (no-ConstRel {n = 1}) w (n<1+n _) x

ShapeRel {n = n} δₘ δ (var i) σ η N a RP RΔ v p x = var-rel δₘ δ i σ η N RP RΔ v p (splitAt n i) ≡.refl x
ShapeRel δₘ δ unit σ η N a RP RΔ unit p x = ⊤
ShapeRel δₘ δ (base s) σ η N a RP RΔ (const c) p x = Prf (Setoid._≈_ (sort-index s) x c)
ShapeRel δₘ δ (σ₁ [+] σ₂) σ η N a RP RΔ (inl v) p x =
  Σ (Shape δₘ FD.∣ LI.as-poly σ₁ δ ∣ η) λ x' →
    ShapeRel δₘ δ σ₁ σ η N a RP RΔ v (<-trans (n<1+n _) p) x' ×
    Prf (Tr.shape≈ δₘ FD.∣ LI.as-poly (σ₁ [+] σ₂) δ ∣ η x (inj₁ x'))
ShapeRel δₘ δ (σ₁ [+] σ₂) σ η N a RP RΔ (inr v) p x =
  Σ (Shape δₘ FD.∣ LI.as-poly σ₂ δ ∣ η) λ x' →
    ShapeRel δₘ δ σ₂ σ η N a RP RΔ v (<-trans (n<1+n _) p) x' ×
    Prf (Tr.shape≈ δₘ FD.∣ LI.as-poly (σ₁ [+] σ₂) δ ∣ η x (inj₂ x'))
ShapeRel δₘ δ (σ₁ [×] σ₂) σ η N a RP RΔ (pair v u) p (x , y) =
  ShapeRel δₘ δ σ₁ σ η N a RP RΔ v (<-trans (s≤s (m≤m+n (size v) (size u))) p) x ×
  ShapeRel δₘ δ σ₂ σ η N a RP RΔ u (<-trans (s≤s (m≤n+m (size u) (size v))) p) y
ShapeRel δₘ δ (σ₁ [→] σ₂) σ η N a RP RΔ v p x = ValRel (σ₁ [→] σ₂) v x
ShapeRel δₘ δ (μ τ) σ η N (acc rs) RP RΔ (roll w) p (Tr.sup y) =
  ShapeRel δₘ δ τ (extend σ (μ (sub (sub-lift σ) τ))) (extend η (inj₂ (mkSort FD.∣ LI.as-poly τ δ ∣ η)))
    (suc (size w)) (rs p)
    (extend-VarRel (ShapeRel δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ) (lower-VarRel p RP))
    (extend-ConstRel RΔ)
    (≡.subst Val (unfold-sub σ τ) w) (s≤s (≤-reflexive (size-subst (unfold-sub σ τ) w))) y

-- The vector over the body's inputs at an application: a source weight, then the closure's cells
-- and the argument as the environment.
body-input : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) → Setoid.Carrier A →
             ∣ 𝔽 (width-env γ') ∣ → ∣ 𝔽 (width v) ∣ → ∣ 𝔽 (suc (width-env γ' + width v)) ∣
body-input γ' v s c z zero    = s
body-input γ' v s c z (suc k) =
  Semimodule._+_ (𝔽 (width-env γ' + width v))
    (mat (M.in₁ {width-env γ'} {width v}) .func c)
    (mat (M.in₂ {width-env γ'} {width v}) .func z) k

-- The dependence relations at the variables, over the value relations there.
record VarDep {Δ n m} {δₘ : Fin m → Obj} {σ : TySub (n + Δ) 0} {η : Fin n → Fin m ⊎ FD.Sort m} {N}
              (RP : VarRel δₘ σ η N) (d : ∀ j → DecoAssign δₘ (η j)) : Set₁ where
  field dep : ∀ j u q x (r : RP .rel j u q x) → ∣ 𝔽 (width u) ∣ → ∣ FibEl δₘ (η j) (d j) x ∣ → Prop

record ConstDep {Δ n} {δ : Fin Δ → Obj} {σ : TySub (n + Δ) 0} (RΔ : ConstRel δ σ) : Set₁ where
  field cdep : ∀ k u x (r : RΔ .crel k u x) → ∣ 𝔽 (width u) ∣ → ∣ δ k .fam .fm x ∣ → Prop

open VarDep public
open ConstDep public

extend-VarDep : ∀ {Δ n m} {δₘ : Fin m → Obj} {σ : TySub (n + Δ) 0} {η : Fin n → Fin m ⊎ FD.Sort m} {N}
                {ρ : type 0} {s : Fin m ⊎ FD.Sort m}
                (R₀ : (u : Val ρ) → size u < N → El δₘ s → Set) (RP : VarRel δₘ σ η N)
                {d : ∀ j → DecoAssign δₘ (extend η s j)} →
                (∀ u q x (r : R₀ u q x) → ∣ 𝔽 (width u) ∣ → ∣ FibEl δₘ s (d zero) x ∣ → Prop) →
                VarDep RP (λ j → d (suc j)) → VarDep (extend-VarRel R₀ RP) d
extend-VarDep R₀ RP D₀ D .dep zero    = D₀
extend-VarDep R₀ RP D₀ D .dep (suc j) = D .dep j

lower-VarDep : ∀ {Δ n m} {δₘ : Fin m → Obj} {σ : TySub (n + Δ) 0} {η : Fin n → Fin m ⊎ FD.Sort m} {N N'} (p : N' < N)
               (RP : VarRel δₘ σ η N) {d} → VarDep RP d → VarDep (lower-VarRel p RP) d
lower-VarDep p RP D .dep j u q = D .dep j u (<-trans q p)

extend-ConstDep : ∀ {Δ n} {δ : Fin Δ → Obj} {σ : TySub (n + Δ) 0} {ρ : type 0} {RΔ : ConstRel δ σ} →
                  ConstDep RΔ → ConstDep (extend-ConstRel {ρ = ρ} RΔ)
extend-ConstDep D .cdep = D .cdep

no-ConstDep : ∀ {n} {σ : TySub (n + 0) 0} → ConstDep (no-ConstRel {n = n} {σ = σ})
no-ConstDep .cdep ()

-- The decoration of the body of a closed μ-type: the carrier's own at the recursive variable.
d₀ : (τ : type 1) → ∀ j → DecoAssign interp.δ∅𝒟 (η₀ τ j)
d₀ τ = Tr.deco-ext interp.δ∅𝒟 (LI.as-poly τ (λ ())) (λ i → lift tt)

mu-VarDep : ∀ {τ N} (R : (u : Val (μ τ)) → size u < N → Ix (μ τ) → Set) →
            (∀ u q x (r : R u q x) → ∣ 𝔽 (width u) ∣ → ∣ Fib (μ τ) x ∣ → Prop) →
            VarDep (mu-VarRel R) (d₀ τ)
mu-VarDep R D .dep zero = D
mu-VarDep R D .dep (suc ())

var-dep : ∀ {Δ n m} (δₘ : Fin m → Obj) (δ : Fin Δ → Obj) (i : Fin (n + Δ)) (σ : TySub (n + Δ) 0)
          (η : Fin n → Fin m ⊎ FD.Sort m) (N : ℕ) (RP : VarRel δₘ σ η N) (RΔ : ConstRel δ σ)
          (d : ∀ j → DecoAssign δₘ (η j)) → VarDep RP d → ConstDep RΔ →
          (v : Val (σ i)) (p : size v < N) (s : Fin n ⊎ Fin Δ) (eq : splitAt n i ≡ s)
          (x : Shape δₘ FD.∣ Var δ s ∣ η) → var-rel δₘ δ i σ η N RP RΔ v p s eq x →
          ∣ 𝔽 (width v) ∣ → ∣ FibSh δₘ (Var δ s) d x ∣ → Prop
var-dep δₘ δ i σ η N RP RΔ d DP DΔ v p (inj₁ j) eq x r o dv =
  DP .dep j _ _ x r (λ k → o (≡.subst Fin (width-subst (≡.sym (≡.cong σ (splitAt⁻¹-↑ˡ eq))) v) k)) dv
var-dep δₘ δ i σ η N RP RΔ d DP DΔ v p (inj₂ k') eq x r o dv =
  DΔ .cdep k' _ x r (λ k → o (≡.subst Fin (width-subst (≡.sym (≡.cong σ (splitAt⁻¹-↑ʳ eq))) v) k)) dv

-- A dependence vector on a value's positions against an element of the fibre at a related index.
-- At an arrow type the root agrees, and for any further source weight, any related argument and
-- any derivation of the body, the body's dependence through the root and the further weight as
-- source and the cells and argument as environment agrees with the elimination constant at that
-- source plus the payload evaluated at the argument plus the index's fibre map at the argument. At
-- a μ-type and at the shapes of an open type, the vector is read against the fibre at the shape as
-- at the closed type formers.
DepRel : ∀ τ {v : Val τ} {i : Ix τ} → ValRel τ v i → ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
MuDepRel : ∀ (τ : type 1) (N : ℕ) (a : Acc _<_ N) {v : Val (μ τ)} {p : size v < N} {i : Ix (μ τ)} →
           MuRel τ N a v p i → ∣ 𝔽 (width v) ∣ → ∣ Fib (μ τ) i ∣ → Prop
ShapeDepRel : ∀ {Δ n m} (δₘ : Fin m → Obj) (δ : Fin Δ → Obj) (τ : type (n + Δ)) (σ : TySub (n + Δ) 0)
              (η : Fin n → Fin m ⊎ FD.Sort m) (N : ℕ) (a : Acc _<_ N) (RP : VarRel δₘ σ η N) (RΔ : ConstRel δ σ)
              (d : ∀ j → DecoAssign δₘ (η j)) → VarDep RP d → ConstDep RΔ →
              {v : Val (sub σ τ)} {p : size v < N} {x : Shape δₘ FD.∣ LI.as-poly τ δ ∣ η} →
              ShapeRel δₘ δ τ σ η N a RP RΔ v p x →
              ∣ 𝔽 (width v) ∣ → ∣ FibSh δₘ (LI.as-poly τ δ) d x ∣ → Prop

DepRel unit {unit} {i} r o d = Semimodule._≈_ (Fib unit i) o d
DepRel (base s) {const c} {i} r o d = Semimodule._≈_ (Fib (base s) i) o d
DepRel (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d in
  (o zero ≈A proj₁ d') ∧ DepRel σ r (λ k → o (suc k)) (proj₂ d')
DepRel (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) o d =
  let d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func d in
  (o zero ≈A proj₁ d') ∧ DepRel τ r (λ k → o (suc k)) (proj₂ d')
DepRel (σ [×] τ) {pair v u} {i , j} (r , r') o d =
  (o zero ≈A proj₁ d) ∧
  (DepRel σ r (mat (M.p₁ {width v} {width u}) .func (λ k → o (suc k))) (proj₁ (proj₂ d)) ∧
   DepRel τ r' (mat (M.p₂ {width v} {width u}) .func (λ k → o (suc k))) (proj₂ (proj₂ d)))
DepRel (σ [→] τ) {clo γ' t} {f} r o d =
  (o zero ≈A proj₁ d) ∧
  (∀ (s' : Setoid.Carrier A) {v : Val σ} {j : Ix σ} (rv : ValRel σ v j)
     (z : ∣ 𝔽 (width v) ∣) (y : ∣ Fib σ j ∣) → DepRel σ rv z y →
   ∀ {u U} (D : γ' · v , t ⇓ u [ U ]) →
     DepRel τ (r rv D) (mat U .func (body-input γ' v (s' Sc.+ o zero) (λ k → o (suc k)) z))
       (Semimodule._+_ (Fib τ (f .idxf .sfunc j))
         (elim-const τ .at (f .idxf .sfunc j) .func (s' Sc.+ o zero))
         (Semimodule._+_ (Fib τ (f .idxf .sfunc j))
           (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ d))
           (f .famf .transf j .func y))))
DepRel (μ τ) {v} {i} r o d = MuDepRel τ (suc (size v)) (<-wellFounded _) {v} {n<1+n _} {i} r o d

MuDepRel τ N (acc rs) {roll w} {p} {Tr.sup x} r o d =
  ShapeDepRel interp.δ∅𝒟 (λ ()) τ (push (μ τ)) (η₀ τ) (suc (size w)) (rs p)
    (mu-VarRel (MuRel τ (suc (size w)) (rs p))) (no-ConstRel {n = 1}) (d₀ τ)
    (mu-VarDep (MuRel τ (suc (size w)) (rs p)) (λ u q x r → MuDepRel τ (suc (size w)) (rs p) {u} {q} {x} r)) (no-ConstDep {n = 1}) r o d

ShapeDepRel {n = n} δₘ δ (var i) σ η N a RP RΔ d DP DΔ {v} {p} {x} r o dv =
  var-dep δₘ δ i σ η N RP RΔ d DP DΔ v p (splitAt n i) ≡.refl x r o dv
ShapeDepRel δₘ δ unit σ η N a RP RΔ d DP DΔ {unit} {x = x} r o dv = Semimodule._≈_ (Fib unit x) o dv
ShapeDepRel δₘ δ (base s) σ η N a RP RΔ d DP DΔ {const c} {x = x} r o dv = Semimodule._≈_ (Fib (base s) x) o dv
ShapeDepRel δₘ δ (σ₁ [+] σ₂) σ η N a RP RΔ d DP DΔ {inl v} {x = x} (x' , r , ⟪ e ⟫) o dv =
  let dv' = Tr.fib-shape-subst δₘ (LI.as-poly (σ₁ [+] σ₂) δ) d {x} {inj₁ x'} e .func dv in
  (o zero ≈A proj₁ dv') ∧ ShapeDepRel δₘ δ σ₁ σ η N a RP RΔ d DP DΔ r (λ k → o (suc k)) (proj₂ dv')
ShapeDepRel δₘ δ (σ₁ [+] σ₂) σ η N a RP RΔ d DP DΔ {inr v} {x = x} (x' , r , ⟪ e ⟫) o dv =
  let dv' = Tr.fib-shape-subst δₘ (LI.as-poly (σ₁ [+] σ₂) δ) d {x} {inj₂ x'} e .func dv in
  (o zero ≈A proj₁ dv') ∧ ShapeDepRel δₘ δ σ₂ σ η N a RP RΔ d DP DΔ r (λ k → o (suc k)) (proj₂ dv')
ShapeDepRel δₘ δ (σ₁ [×] σ₂) σ η N a RP RΔ d DP DΔ {pair v u} {x = x , y} (r , r') o dv =
  (o zero ≈A proj₁ dv) ∧
  (ShapeDepRel δₘ δ σ₁ σ η N a RP RΔ d DP DΔ r (mat (M.p₁ {width v} {width u}) .func (λ k → o (suc k))) (proj₁ (proj₂ dv)) ∧
   ShapeDepRel δₘ δ σ₂ σ η N a RP RΔ d DP DΔ r' (mat (M.p₂ {width v} {width u}) .func (λ k → o (suc k))) (proj₂ (proj₂ dv)))
ShapeDepRel δₘ δ (σ₁ [→] σ₂) σ η N a RP RΔ d DP DΔ {v} {x = x} r o dv = DepRel (σ₁ [→] σ₂) {v} {x} r o dv
ShapeDepRel δₘ δ (μ τ) σ η N (acc rs) RP RΔ d DP DΔ {roll w} {p} {Tr.sup y} r o dv =
  ShapeDepRel δₘ δ τ (extend σ (μ (sub (sub-lift σ) τ))) (extend η (inj₂ (mkSort FD.∣ LI.as-poly τ δ ∣ η)))
    (suc (size w)) (rs p)
    (extend-VarRel (ShapeRel δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ) (lower-VarRel p RP))
    (extend-ConstRel RΔ) (Tr.deco-ext δₘ (LI.as-poly τ δ) d)
    (extend-VarDep (ShapeRel δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ) (lower-VarRel p RP)
       (λ u q x r → ShapeDepRel δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ d (lower-VarDep p RP DP) DΔ {u} {q} {x} r)
       (lower-VarDep p RP DP))
    (extend-ConstDep DΔ) r (λ k → o (≡.subst Fin (width-subst (unfold-sub σ τ) w) k)) dv

-- A primitive's arguments need no relations of their own. The model's index at a tuple of
-- arguments is a tuple of sort indices, and sort-vals-setoid is built from ⊗-setoid, whose
-- equality is the pairwise conjunction, so the value relation is equality in that setoid, one
-- base equation per argument. The fibre is 𝔽 (bases-width is) on both sides, the arguments'
-- positions laid end to end, so the vector relation is equality there, as at a single base sort.

-- Environments related to context indices, and environment vectors to elements of the context
-- fibre at a source weight: each cell may carry, beyond its relation, control dependence below the
-- elimination constant at the source.
data EnvValRel : ∀ {Γ} → Env Γ → IxC Γ → Set where
  emp : EnvValRel emp (lift tt)
  _·_ : ∀ {Γ τ} {γ : Env Γ} {v : Val τ} {gi i} → EnvValRel γ gi → ValRel τ v i → EnvValRel (γ · v) (gi , i)

infixl 30 _·_

-- The elimination constant at an index and source weight.
ec : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣
ec τ i s = elim-const τ .at i .func s

-- Each fibre's semimodule with its additive order: x ⊑ y when x + y is y. Addition in a fibre is
-- idempotent because it is in the semiring.
fib-+-idem : ∀ τ i {x} → Semimodule._≈_ (Fib τ i) (Semimodule._+_ (Fib τ i) x x) x
fib-+-idem τ i =
  X.trans (X.+-cong (X.sym X.·-unit) (X.sym X.·-unit))
          (X.trans (X.sym X.+-distribʳ) (X.trans (X.·-cong (+-idem Sc.ι) X.refl) X.·-unit))
  where module X = Semimodule (Fib τ i)

module F τ i where
  open Semimodule (Fib τ i) public
  open commutative-monoid.AdditivePreorder additive (fib-+-idem τ i) public

-- The dependence relation up to control dependence below the elimination constant at the source.
DepRel⊑ : ∀ τ {v : Val τ} {i : Ix τ} → ValRel τ v i → Setoid.Carrier A →
          ∣ 𝔽 (width v) ∣ → ∣ Fib τ i ∣ → Prop
DepRel⊑ τ {i = i} r s o d =
  ∃ (∣ Fib τ i ∣) (λ m → F._⊑_ τ i m (ec τ i s) ∧ DepRel τ r o (Semimodule._+_ (Fib τ i) d m))

EnvDepRel : ∀ {Γ} {γ : Env Γ} {gi} → EnvValRel γ gi → Setoid.Carrier A →
            ∣ 𝔽 (width-env γ) ∣ → ∣ FibC Γ gi ∣ → Prop
EnvDepRel emp s x g = prop.⊤
EnvDepRel (_·_ {τ = τ} {γ = γ} {v = v} rγ r) s x g =
  EnvDepRel rγ s (mat (M.p₁ {width-env γ} {width v}) .func x) (proj₁ g) ∧
  DepRel⊑ τ r s (mat (M.p₂ {width-env γ} {width v}) .func x) (proj₂ g)

-- The inputs of a derivation: the source weight at the first position, the environment after.
inputs : ∀ {Γ} (γ : Env Γ) → Setoid.Carrier A → ∣ 𝔽 (width-env γ) ∣ → ∣ 𝔽 (suc (width-env γ)) ∣
inputs γ s x zero    = s
inputs γ s x (suc k) = x k

open model using (app-+ₘ; app-∘; app-εₘ; app-I; app-e; app-congₘ; app-congᵥ) renaming (app to ap)
open Sc using (ι; ε) renaming (_≈_ to _≈s_; _+_ to _+ₛ_; _·_ to _·ₛ_)
open Setoid A using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open M using (Σ-cong; Σ-unit; Σ-ε; _∘_; _+ₘ_; εₘ; ≈ₘ-refl; ≈ₘ-sym; ≈ₘ-trans) renaming (Σ to Σₛ)

open Sc using (+-cong; ·-cong; +-lunit; +-comm; +-assoc; ·-lunit; ·-comm; ε-annihilₗ; ε-annihilᵣ)
open M using (⟨_,_⟩)

-- Reading a relation at the inputs: the source column at the source weight, and the environment
-- columns at the environment vector.
p₁-e : ∀ {m} (j : Fin (suc m)) → M.p₁ {1} {m} zero j ≈s M.e zero j
p₁-e zero    = ≈-refl
p₁-e (suc j) = ≈-refl

p₂-e : ∀ {m} (j : Fin m) (l : Fin m) → M.p₂ {1} {m} j (suc l) ≈s M.e j l
p₂-e j l = ≈-refl

-- Semiring shorthands.
w = elim-weight
+-runit : ∀ {x} → (x +ₛ ε) ≈s x
+-runit = ≈-trans +-comm +-lunit
·-runit : ∀ {x} → (x ·ₛ ι) ≈s x
·-runit = ≈-trans ·-comm ·-lunit
Σ₁ : ∀ (f : Fin 1 → Setoid.Carrier A) → Σₛ f ≈s f zero
Σ₁ f = +-runit

-- The same in a semimodule.
m-lunit : ∀ (X : Semimodule) {x} → Semimodule._≈_ X (Semimodule._+_ X (Semimodule.ε X) x) x
m-lunit X = Semimodule.+-lunit X
m-runit : ∀ (X : Semimodule) {x} → Semimodule._≈_ X (Semimodule._+_ X x (Semimodule.ε X)) x
m-runit X = Semimodule.trans X (Semimodule.+-comm X) (Semimodule.+-lunit X)

-- Reading a lifted vector: the first position of the first summand's injection, and the rest of
-- the second's.
ap-in₁-zero : ∀ {n} (u : ∣ 𝔽 1 ∣) → ap (M.in₁ {1} {n}) u zero ≈s u zero
ap-in₁-zero {n} u = ≈-trans (Σ₁ (λ j → M.in₁ {1} {n} zero j ·ₛ u j)) ·-lunit

ap-in₁-suc : ∀ {n} (u : ∣ 𝔽 1 ∣) (k : Fin n) → ap (M.in₁ {1} {n}) u (suc k) ≈s ε
ap-in₁-suc {n} u k = ≈-trans (Σ₁ (λ j → M.in₁ {1} {n} (suc k) j ·ₛ u j)) ε-annihilₗ

ap-in₂-zero : ∀ {n} (u : ∣ 𝔽 n ∣) → ap (M.in₂ {1} {n}) u zero ≈s ε
ap-in₂-zero {n} u = ≈-trans (Σ-cong {n} (λ _ → ε-annihilₗ)) (Σ-ε {n})

ap-in₂-suc : ∀ {n} (u : ∣ 𝔽 n ∣) (k : Fin n) → ap (M.in₂ {1} {n}) u (suc k) ≈s u k
ap-in₂-suc {n} u k =
  ≈-trans (Σ-cong {n} (λ j → ·-cong (≈-trans (p₂-e {n} j k) (M.e-sym j k)) ≈-refl)) (Σ-unit {n} k u)

ap-pair-zero : ∀ {m n} (f : M.Matrix 1 m) (g : M.Matrix n m) (u : ∣ 𝔽 m ∣) →
               ap (⟨ f , g ⟩) u zero ≈s ap f u zero
ap-pair-zero {m} {n} f g u =
  ≈-trans (app-+ₘ (M.in₁ {1} {n} ∘ f) (M.in₂ {1} {n} ∘ g) u zero)
          (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) f u zero) (ap-in₁-zero {n} (ap f u)))
                           (≈-trans (app-∘ (M.in₂ {1} {n}) g u zero) (ap-in₂-zero {n} (ap g u))))
                   +-runit)

ap-pair-suc : ∀ {m n} (f : M.Matrix 1 m) (g : M.Matrix n m) (u : ∣ 𝔽 m ∣) (k : Fin n) →
              ap (⟨ f , g ⟩) u (suc k) ≈s ap g u k
ap-pair-suc {m} {n} f g u k =
  ≈-trans (app-+ₘ (M.in₁ {1} {n} ∘ f) (M.in₂ {1} {n} ∘ g) u (suc k))
          (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) f u (suc k)) (ap-in₁-suc {n} (ap f u) k))
                           (≈-trans (app-∘ (M.in₂ {1} {n}) g u (suc k)) (ap-in₂-suc {n} (ap g u) k)))
                   +-lunit)

-- The control vector at a source weight: the weight at the root of a lifted value, and the
-- payload's control vector after.
ap-ctrl-row : ∀ {n} (s : Setoid.Carrier A) (k : Fin n) → ap ctrl-row (λ _ → s) k ≈s (w ·ₛ s)
ap-ctrl-row {n} s k = Σ₁ (λ j → ctrl-row {n} k j ·ₛ s)

ctrl-lift-zero : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) →
                 ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) zero ≈s (w ·ₛ s)
ctrl-lift-zero {n} g s = ≈-trans (ap-pair-zero {1} {n} ctrl-row g (λ _ → s)) (ap-ctrl-row {1} s zero)

ctrl-lift-suc : ∀ {n} (g : M.Matrix n 1) (s : Setoid.Carrier A) (k : Fin n) →
                ap (⟨ ctrl-row {1} , g ⟩) (λ _ → s) (suc k) ≈s ap g (λ _ → s) k
ctrl-lift-suc {n} g s k = ap-pair-suc {1} {n} ctrl-row g (λ _ → s) k

-- Reading a relation at the inputs: the source column at the source weight and the environment
-- columns at the environment vector, and the relations the rules are built from at any vector.
ap-p₁₁ : ∀ {m} (o : ∣ 𝔽 (suc m) ∣) (k : Fin 1) → ap (M.p₁ {1} {m}) o k ≈s o zero
ap-p₁₁ {m} o zero =
  ≈-trans (Σ-cong {suc m} (λ j → ·-cong (p₁-e {m} j) (≈-refl {o j}))) (Σ-unit {suc m} zero o)

ap-p₂₁ : ∀ {m} (o : ∣ 𝔽 (suc m) ∣) (k : Fin m) → ap (M.p₂ {1} {m}) o k ≈s o (suc k)
ap-p₂₁ {m} o k =
  ≈-trans (+-cong ε-annihilₗ (Σ-cong {m} (λ j → ·-cong (p₂-e {m} k j) ≈-refl)))
          (≈-trans +-lunit (Σ-unit {m} k (λ j → o (suc j))))

inputs-in : ∀ {Γ} (γ : Env Γ) s x (l : Fin (suc (width-env γ))) →
            inputs γ s x l ≈s
            (ap (M.in₁ {1} {width-env γ}) (λ _ → s) l +ₛ ap (M.in₂ {1} {width-env γ}) x l)
inputs-in γ s x zero =
  ≈-sym (≈-trans (+-cong (ap-in₁-zero {width-env γ} (λ _ → s)) (ap-in₂-zero {width-env γ} x)) +-runit)
inputs-in γ s x (suc l) =
  ≈-sym (≈-trans (+-cong (ap-in₁-suc {width-env γ} (λ _ → s) l) (ap-in₂-suc {width-env γ} x l)) +-lunit)

app-inputs : ∀ {Γ} {γ : Env Γ} {n} (R : M.Matrix n (suc (width-env γ))) s x (k : Fin n) →
             ap R (inputs γ s x) k ≈s
             (ap (R ∘ M.in₁ {1} {width-env γ}) (λ _ → s) k +ₛ ap (R ∘ M.in₂ {1} {width-env γ}) x k)
app-inputs {γ = γ} R s x k =
  ≈-trans (app-congᵥ R (inputs-in γ s x) k)
  (≈-trans (model.app-+ R (ap (M.in₁ {1} {width-env γ}) (λ _ → s)) (ap (M.in₂ {1} {width-env γ}) x) k)
           (+-cong (≈-sym (app-∘ R (M.in₁ {1} {width-env γ}) (λ _ → s) k))
                   (≈-sym (app-∘ R (M.in₂ {1} {width-env γ}) x k))))

ap-∥ : ∀ {m n} (A : M.Matrix n 1) (B : M.Matrix n m) (y : ∣ 𝔽 (suc m) ∣) (k : Fin n) →
       ap (A M.∥ B) y k ≈s (ap A (λ _ → y zero) k +ₛ ap B (λ l → y (suc l)) k)
ap-∥ {m} A B y k =
  ≈-trans (app-+ₘ (A ∘ M.p₁ {1} {m}) (B ∘ M.p₂ {1} {m}) y k)
          (+-cong (≈-trans (app-∘ A (M.p₁ {1} {m}) y k) (app-congᵥ A (ap-p₁₁ {m} y) k))
                  (≈-trans (app-∘ B (M.p₂ {1} {m}) y k) (app-congᵥ B (ap-p₂₁ {m} y) k)))

ap-wsrc : ∀ {m n} (y : ∣ 𝔽 (suc m) ∣) (k : Fin n) → ap (wsrc {m} {n}) y k ≈s (w ·ₛ y zero)
ap-wsrc {m} {n} y k =
  ≈-trans (app-∘ (ctrl-row {n}) (M.p₁ {1} {m}) y k)
          (≈-trans (app-congᵥ (ctrl-row {n}) (ap-p₁₁ {m} y) k) (ap-ctrl-row {n} (y zero) k))

ap-⊕-zero : ∀ {m a b} (f : M.Matrix 1 a) (g : M.Matrix b m) (y : ∣ 𝔽 (a + m) ∣) →
            ap (f ⊕ g) y zero ≈s ap f (ap (M.p₁ {a} {m}) y) zero
ap-⊕-zero {m} {a} {b} f g y =
  ≈-trans (ap-pair-zero {a + m} {b} (f ∘ M.p₁ {a} {m}) (g ∘ M.p₂ {a} {m}) y)
          (app-∘ f (M.p₁ {a} {m}) y zero)

ap-⊕-suc : ∀ {m a b} (f : M.Matrix 1 a) (g : M.Matrix b m) (y : ∣ 𝔽 (a + m) ∣) (k : Fin b) →
           ap (f ⊕ g) y (suc k) ≈s ap g (ap (M.p₂ {a} {m}) y) k
ap-⊕-suc {m} {a} {b} f g y k =
  ≈-trans (ap-pair-suc {a + m} {b} (f ∘ M.p₁ {a} {m}) (g ∘ M.p₂ {a} {m}) y k)
          (app-∘ g (M.p₂ {a} {m}) y k)

ap-⊕₁-zero : ∀ {m b} (f : M.Matrix 1 1) (g : M.Matrix b m) (y : ∣ 𝔽 (suc m) ∣) →
             ap (f ⊕ g) y zero ≈s ap f (λ _ → y zero) zero
ap-⊕₁-zero {m} f g y = ≈-trans (ap-⊕-zero {m} {1} f g y) (app-congᵥ f (ap-p₁₁ {m} y) zero)

ap-⊕₁-suc : ∀ {m b} (f : M.Matrix 1 1) (g : M.Matrix b m) (y : ∣ 𝔽 (suc m) ∣) (k : Fin b) →
            ap (f ⊕ g) y (suc k) ≈s ap g (λ l → y (suc l)) k
ap-⊕₁-suc {m} f g y k = ≈-trans (ap-⊕-suc {m} {1} f g y k) (app-congᵥ g (ap-p₂₁ {m} y) k)

-- The elimination constant elementwise: the weight times the source at each root, the payload's
-- constant under it, and zero at a closure's payload.
ec-unit : ∀ i s → ec unit i s zero ≈s (w ·ₛ s)
ec-unit i s =
  ≈-trans (+-cong (·-cong +-runit ≈-refl) ≈-refl)
          (≈-trans +-runit (≈-trans ·-lunit +-runit))

-- The same at a base sort: the sort's unit constant is the row of units, so scaling by the
-- elimination weight leaves the weight at every position of the result.
ec-base : ∀ {σ} i s (k : Fin (sort-width σ)) → ec (base σ) i s k ≈s (w ·ₛ s)
ec-base i s k = ≈-trans +-runit (≈-trans ·-lunit +-runit)

ec-inj₁ : ∀ {σ τ} (i : Ix σ) s →
          (proj₁ (ec (σ [+] τ) (inj₁ i) s) ≈s (w ·ₛ s)) ∧
          Semimodule._≈_ (Fib σ i) (proj₂ (ec (σ [+] τ) (inj₁ i) s)) (ec σ i s)
ec-inj₁ {σ} i s = ≈-trans +-runit +-runit , Semimodule.+-lunit (Fib σ i)

ec-inj₂ : ∀ {σ τ} (i : Ix τ) s →
          (proj₁ (ec (σ [+] τ) (inj₂ i) s) ≈s (w ·ₛ s)) ∧
          Semimodule._≈_ (Fib τ i) (proj₂ (ec (σ [+] τ) (inj₂ i) s)) (ec τ i s)
ec-inj₂ {σ} {τ} i s = ≈-trans +-runit +-runit , Semimodule.+-lunit (Fib τ i)

ec-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s →
          (proj₁ (ec (σ [×] τ) (i , j) s) ≈s (w ·ₛ s)) ∧
          (Semimodule._≈_ (Fib σ i) (proj₁ (proj₂ (ec (σ [×] τ) (i , j) s))) (ec σ i s) ∧
           Semimodule._≈_ (Fib τ j) (proj₂ (proj₂ (ec (σ [×] τ) (i , j) s))) (ec τ j s))
ec-pair {σ} {τ} i j s =
  ≈-trans +-runit +-runit ,
  (Semimodule.trans (Fib σ i) (m-lunit (Fib σ i)) (m-runit (Fib σ i)) ,
   Semimodule.trans (Fib τ j) (m-lunit (Fib τ j)) (m-lunit (Fib τ j)))

ec-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s →
         (proj₁ (ec (σ [→] τ) f s) ≈s (w ·ₛ s)) ∧
         Semimodule._≈_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (proj₂ (ec (σ [→] τ) f s))
           (Semimodule.ε (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f))
ec-clo {σ} {τ} f s =
  ≈-trans +-runit +-runit ,
  m-lunit (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) {Semimodule.ε (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f)}

ec-natural : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s →
             Semimodule._≈_ (Fib τ i') (⟦ τ ⟧ .fam .subst e .func (ec τ i s)) (ec τ i' s)
ec-natural τ e s = elim-const τ .Constant.at-natural e .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq ≈-refl

-- The fibre relation respects the setoids on both sides.
body-input-resp : ∀ {Γ' σ} (γ' : Env Γ') (v : Val σ) {s s' c c' z} →
                  s ≈s s' → (∀ k → c k ≈s c' k) → ∀ k →
                  body-input γ' v s c z k ≈s body-input γ' v s' c' z k
body-input-resp γ' v es ec zero    = es
body-input-resp γ' v es ec (suc k) =
  +-cong (app-congᵥ (M.in₁ {width-env γ'} {width v}) ec k) ≈-refl

-- The dependence relations at the variables respect the setoids on both sides.
VarDep-resp : ∀ {Δ n m} {δₘ : Fin m → Obj} {σ : TySub (n + Δ) 0} {η : Fin n → Fin m ⊎ FD.Sort m} {N}
              {RP : VarRel δₘ σ η N} {d : ∀ j → DecoAssign δₘ (η j)} → VarDep RP d → Prop
VarDep-resp {δₘ = δₘ} {η = η} {RP = RP} {d} DP =
  ∀ j u q x (r : RP .rel j u q x) {o o' : ∣ 𝔽 (width u) ∣} {dv dv'} →
  (∀ k → o k ≈s o' k) → Semimodule._≈_ (FibEl δₘ (η j) (d j) x) dv dv' →
  DP .dep j u q x r o dv → DP .dep j u q x r o' dv'

ConstDep-resp : ∀ {Δ n} {δ : Fin Δ → Obj} {σ : TySub (n + Δ) 0} {RΔ : ConstRel δ σ} → ConstDep RΔ → Prop
ConstDep-resp {δ = δ} {RΔ = RΔ} DΔ =
  ∀ k u x (r : RΔ .crel k u x) {o o' : ∣ 𝔽 (width u) ∣} {dv dv'} →
  (∀ k' → o k' ≈s o' k') → Semimodule._≈_ (δ k .fam .fm x) dv dv' →
  DΔ .cdep k u x r o dv → DΔ .cdep k u x r o' dv'

extend-VarDep-resp : ∀ {Δ n m} {δₘ : Fin m → Obj} {σ : TySub (n + Δ) 0} {η : Fin n → Fin m ⊎ FD.Sort m} {N}
                     {ρ : type 0} {s : Fin m ⊎ FD.Sort m}
                     {R₀ : (u : Val ρ) → size u < N → El δₘ s → Set} {RP : VarRel δₘ σ η N}
                     {d : ∀ j → DecoAssign δₘ (extend η s j)}
                     (D₀ : ∀ u q x (r : R₀ u q x) → ∣ 𝔽 (width u) ∣ → ∣ FibEl δₘ s (d zero) x ∣ → Prop)
                     (DP : VarDep RP (λ j → d (suc j))) →
                     (∀ u q x (r : R₀ u q x) {o o' : ∣ 𝔽 (width u) ∣} {dv dv'} →
                       (∀ k → o k ≈s o' k) → Semimodule._≈_ (FibEl δₘ s (d zero) x) dv dv' →
                       D₀ u q x r o dv → D₀ u q x r o' dv') →
                     VarDep-resp DP → VarDep-resp (extend-VarDep R₀ RP {d = d} D₀ DP)
extend-VarDep-resp D₀ DP H₀ H zero    = H₀
extend-VarDep-resp D₀ DP H₀ H (suc j) = H j

lower-VarDep-resp : ∀ {Δ n m} {δₘ : Fin m → Obj} {σ : TySub (n + Δ) 0} {η : Fin n → Fin m ⊎ FD.Sort m} {N N'}
                    (p : N' < N) {RP : VarRel δₘ σ η N} {d} (DP : VarDep RP d) →
                    VarDep-resp DP → VarDep-resp (lower-VarDep p RP DP)
lower-VarDep-resp p DP H j u q = H j u (<-trans q p)

extend-ConstDep-resp : ∀ {Δ n} {δ : Fin Δ → Obj} {σ : TySub (n + Δ) 0} (ρ : type 0) {RΔ : ConstRel δ σ}
                       (DΔ : ConstDep RΔ) → ConstDep-resp DΔ → ConstDep-resp (extend-ConstDep {ρ = ρ} DΔ)
extend-ConstDep-resp ρ DΔ H = H

no-ConstDep-resp : ∀ {n} {σ : TySub (n + 0) 0} → ConstDep-resp (no-ConstDep {n = n} {σ = σ})
no-ConstDep-resp ()

DepRel-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) {o o' : ∣ 𝔽 (width v) ∣} {d d' : ∣ Fib τ i ∣} →
              (∀ k → o k ≈s o' k) → F._≈_ τ i d d' → DepRel τ r o d → DepRel τ r o' d'
MuDepRel-resp : ∀ τ N (a : Acc _<_ N) {v : Val (μ τ)} {p : size v < N} {i : Ix (μ τ)} (r : MuRel τ N a v p i)
                {o o' : ∣ 𝔽 (width v) ∣} {d d' : ∣ Fib (μ τ) i ∣} →
                (∀ k → o k ≈s o' k) → F._≈_ (μ τ) i d d' → MuDepRel τ N a r o d → MuDepRel τ N a r o' d'
ShapeDepRel-resp : ∀ {Δ n m} (δₘ : Fin m → Obj) (δ : Fin Δ → Obj) (τ : type (n + Δ)) (σ : TySub (n + Δ) 0)
                   (η : Fin n → Fin m ⊎ FD.Sort m) (N : ℕ) (a : Acc _<_ N) (RP : VarRel δₘ σ η N) (RΔ : ConstRel δ σ)
                   (d : ∀ j → DecoAssign δₘ (η j)) (DP : VarDep RP d) (DΔ : ConstDep RΔ) →
                   VarDep-resp DP → ConstDep-resp DΔ →
                   {v : Val (sub σ τ)} {p : size v < N} {x : Shape δₘ FD.∣ LI.as-poly τ δ ∣ η}
                   (r : ShapeRel δₘ δ τ σ η N a RP RΔ v p x) {o o' : ∣ 𝔽 (width v) ∣}
                   {dv dv' : ∣ FibSh δₘ (LI.as-poly τ δ) d x ∣} →
                   (∀ k → o k ≈s o' k) → Semimodule._≈_ (FibSh δₘ (LI.as-poly τ δ) d x) dv dv' →
                   ShapeDepRel δₘ δ τ σ η N a RP RΔ d DP DΔ r o dv → ShapeDepRel δₘ δ τ σ η N a RP RΔ d DP DΔ r o' dv'

DepRel-resp unit {unit} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
DepRel-resp (base s) {const c} r eo ed h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (ed k))
DepRel-resp (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .SemiMod._⇒_.func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (prop._∧_.proj₁ ed')) ,
  DepRel-resp σ r (λ k → eo (suc k)) (prop._∧_.proj₂ ed') h
DepRel-resp (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) {d = d} {d'} eo ed (h₀ , h) =
  let ed' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .SemiMod._⇒_.func-resp-≈ ed in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (prop._∧_.proj₁ ed')) ,
  DepRel-resp τ r (λ k → eo (suc k)) (prop._∧_.proj₂ ed') h
DepRel-resp (σ [×] τ) {pair v u} {i , j} (r , r') eo (ed₀ , (ed₁ , ed₂)) (h₀ , (h₁ , h₂)) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  (DepRel-resp σ r (app-congᵥ (M.p₁ {width v} {width u}) (λ k → eo (suc k))) ed₁ h₁ ,
   DepRel-resp τ r' (app-congᵥ (M.p₂ {width v} {width u}) (λ k → eo (suc k))) ed₂ h₂)
DepRel-resp (σ [→] τ) {clo γ' t} {f} r {o} {o'} {d} {d'} eo (ed₀ , ed₂) (h₀ , hc) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp τ (r rv D)
      (app-congᵥ U (body-input-resp γ' v (+-cong ≈-refl (eo zero)) (λ k → eo (suc k))))
      (F.+-cong τ (f .idxf .sfunc j)
         (elim-const τ .at (f .idxf .sfunc j) .SemiMod._⇒_.func-resp-≈ (+-cong ≈-refl (eo zero)))
         (F.+-cong τ (f .idxf .sfunc j)
            (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
               {proj₂ d} {proj₂ d'} ed₂)
            (F.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc s' rv z y hz D)
DepRel-resp (μ τ) {v} {i} r eo ed h = MuDepRel-resp τ (suc (size v)) (<-wellFounded _) {v} {n<1+n _} {i} r eo ed h

MuDepRel-resp τ N (acc rs) {roll w} {p} {Tr.sup x} r eo ed h =
  ShapeDepRel-resp interp.δ∅𝒟 (λ ()) τ (push (μ τ)) (η₀ τ) (suc (size w)) (rs p)
    (mu-VarRel (MuRel τ (suc (size w)) (rs p))) (no-ConstRel {n = 1}) (d₀ τ)
    (mu-VarDep (MuRel τ (suc (size w)) (rs p)) (λ u q x r → MuDepRel τ (suc (size w)) (rs p) {u} {q} {x} r))
    (no-ConstDep {n = 1}) H (no-ConstDep-resp {n = 1}) r eo ed h
  where
  H : VarDep-resp (mu-VarDep (MuRel τ (suc (size w)) (rs p)) (λ u q x r → MuDepRel τ (suc (size w)) (rs p) {u} {q} {x} r))
  H zero u q x r = MuDepRel-resp τ (suc (size w)) (rs p) {u} {q} {x} r
  H (suc ())

ShapeDepRel-resp {Δ} {n} δₘ δ (var i) σ η N a RP RΔ d DP DΔ HP HΔ {v} {p} {x} r eo edv h =
  go (splitAt n i) ≡.refl x r eo edv h
  where
  go : ∀ (s : Fin n ⊎ Fin Δ) (eq : splitAt n i ≡ s) (x : Shape δₘ FD.∣ Var δ s ∣ η)
       (r : var-rel δₘ δ i σ η N RP RΔ v p s eq x) {o o' : ∣ 𝔽 (width v) ∣} {dv dv'} →
       (∀ k → o k ≈s o' k) → Semimodule._≈_ (FibSh δₘ (Var δ s) d x) dv dv' →
       var-dep δₘ δ i σ η N RP RΔ d DP DΔ v p s eq x r o dv → var-dep δₘ δ i σ η N RP RΔ d DP DΔ v p s eq x r o' dv'
  go (inj₁ j) eq x r eo edv h = HP j _ _ x r (λ k → eo _) edv h
  go (inj₂ k) eq x r eo edv h = HΔ k _ x r (λ k' → eo _) edv h
ShapeDepRel-resp δₘ δ unit σ η N a RP RΔ d DP DΔ HP HΔ {unit} r eo edv h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (edv k))
ShapeDepRel-resp δₘ δ (base s) σ η N a RP RΔ d DP DΔ HP HΔ {const c} r eo edv h k = ≈-trans (≈-sym (eo k)) (≈-trans (h k) (edv k))
ShapeDepRel-resp δₘ δ (σ₁ [+] σ₂) σ η N a RP RΔ d DP DΔ HP HΔ {inl v} {x = x} (x' , r , ⟪ e ⟫) eo edv (h₀ , h) =
  let edv' = Tr.fib-shape-subst δₘ (LI.as-poly (σ₁ [+] σ₂) δ) d {x} {inj₁ x'} e .SemiMod._⇒_.func-resp-≈ edv in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (prop._∧_.proj₁ edv')) ,
  ShapeDepRel-resp δₘ δ σ₁ σ η N a RP RΔ d DP DΔ HP HΔ r (λ k → eo (suc k)) (prop._∧_.proj₂ edv') h
ShapeDepRel-resp δₘ δ (σ₁ [+] σ₂) σ η N a RP RΔ d DP DΔ HP HΔ {inr v} {x = x} (x' , r , ⟪ e ⟫) eo edv (h₀ , h) =
  let edv' = Tr.fib-shape-subst δₘ (LI.as-poly (σ₁ [+] σ₂) δ) d {x} {inj₂ x'} e .SemiMod._⇒_.func-resp-≈ edv in
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ (prop._∧_.proj₁ edv')) ,
  ShapeDepRel-resp δₘ δ σ₂ σ η N a RP RΔ d DP DΔ HP HΔ r (λ k → eo (suc k)) (prop._∧_.proj₂ edv') h
ShapeDepRel-resp δₘ δ (σ₁ [×] σ₂) σ η N a RP RΔ d DP DΔ HP HΔ {pair v u} {x = x , y} (r , r') eo (ed₀ , (ed₁ , ed₂)) (h₀ , (h₁ , h₂)) =
  ≈-trans (≈-sym (eo zero)) (≈-trans h₀ ed₀) ,
  (ShapeDepRel-resp δₘ δ σ₁ σ η N a RP RΔ d DP DΔ HP HΔ r (app-congᵥ (M.p₁ {width v} {width u}) (λ k → eo (suc k))) ed₁ h₁ ,
   ShapeDepRel-resp δₘ δ σ₂ σ η N a RP RΔ d DP DΔ HP HΔ r' (app-congᵥ (M.p₂ {width v} {width u}) (λ k → eo (suc k))) ed₂ h₂)
ShapeDepRel-resp δₘ δ (σ₁ [→] σ₂) σ η N a RP RΔ d DP DΔ HP HΔ {v} {x = x} r eo edv h = DepRel-resp (σ₁ [→] σ₂) {v} {x} r eo edv h
ShapeDepRel-resp δₘ δ (μ τ) σ η N (acc rs) RP RΔ d DP DΔ HP HΔ {roll w} {p} {Tr.sup y} r eo edv h =
  ShapeDepRel-resp δₘ δ τ (extend σ (μ (sub (sub-lift σ) τ))) (extend η (inj₂ (mkSort FD.∣ LI.as-poly τ δ ∣ η)))
    (suc (size w)) (rs p)
    (extend-VarRel (ShapeRel δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ) (lower-VarRel p RP))
    (extend-ConstRel RΔ) (Tr.deco-ext δₘ (LI.as-poly τ δ) d)
    (extend-VarDep (ShapeRel δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ) (lower-VarRel p RP)
       (λ u q x r → ShapeDepRel δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ d (lower-VarDep p RP DP) DΔ {u} {q} {x} r)
       (lower-VarDep p RP DP))
    (extend-ConstDep DΔ)
    (extend-VarDep-resp
       (λ u q x r → ShapeDepRel δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ d (lower-VarDep p RP DP) DΔ {u} {q} {x} r)
       (lower-VarDep p RP DP)
       (λ u q x r → ShapeDepRel-resp δₘ δ (μ τ) σ η (suc (size w)) (rs p) (lower-VarRel p RP) RΔ d
                      (lower-VarDep p RP DP) DΔ (lower-VarDep-resp p DP HP) HΔ {u} {q} {x} r)
       (lower-VarDep-resp p DP HP))
    (extend-ConstDep-resp (μ (sub (sub-lift σ) τ)) DΔ HΔ) r (λ k → eo _) edv h

-- Transport of a sum of the constant and an element along an index equation.
subst-ec+ : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s d →
            F._≈_ τ i' (⟦ τ ⟧ .fam .subst e .func (F._+_ τ i (ec τ i s) d))
                       (F._+_ τ i' (ec τ i' s) (⟦ τ ⟧ .fam .subst e .func d))
subst-ec+ τ {i} {i'} e s d =
  F.trans τ i' (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.preserve-+ {ec τ i s} {d})
               (F.+-cong τ i' (ec-natural τ e s) (F.refl τ i'))

app-+ᵥ : ∀ {m n} (R : M.Matrix m n) (u v : ∣ 𝔽 n ∣) (k : Fin m) →
         ap R (λ j → u j +ₛ v j) k ≈s (ap R u k +ₛ ap R v k)
app-+ᵥ R u v k = model.app-+ R u v k

ap-pair-p₁ : ∀ {m a b} (f : M.Matrix a m) (g : M.Matrix b m) (u : ∣ 𝔽 m ∣) (k : Fin a) →
             ap (M.p₁ {a} {b}) (ap (⟨ f , g ⟩) u) k ≈s ap f u k
ap-pair-p₁ {m} {a} {b} f g u k =
  ≈-trans (≈-sym (app-∘ (M.p₁ {a} {b}) (⟨ f , g ⟩) u k))
          (app-congₘ (HasProducts.pair-p₁ M.products f g) u k)

ap-pair-p₂ : ∀ {m a b} (f : M.Matrix a m) (g : M.Matrix b m) (u : ∣ 𝔽 m ∣) (k : Fin b) →
             ap (M.p₂ {a} {b}) (ap (⟨ f , g ⟩) u) k ≈s ap g u k
ap-pair-p₂ {m} {a} {b} f g u k =
  ≈-trans (≈-sym (app-∘ (M.p₂ {a} {b}) (⟨ f , g ⟩) u k))
          (app-congₘ (HasProducts.pair-p₂ M.products f g) u k)

-- Adding the value's control positions at a source weight on the operational side, and the
-- elimination constant on the denotational side, preserves the relation.
ctrl-add : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) (s : Setoid.Carrier A)
           {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} → DepRel τ r o d →
           DepRel τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (F._+_ τ i (ec τ i s) d)
ctrl-add unit {unit} {i} r s h zero =
  +-cong (≈-trans (ap-ctrl-row {1} s zero) (≈-sym (ec-unit i s))) (h zero)
ctrl-add (base σ) {const c} {i} r s h k =
  +-cong (≈-trans (ap-ctrl-row {sort-width σ} s k) (≈-sym (ec-base i s k))) (h k)
ctrl-add (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ec+ (σ [+] τ) {i} {inj₁ i'} e s d
      d' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func d
  in
  ≈-trans (+-cong (ctrl-lift-zero (ctrl-of v) s) h₀)
          (≈-sym (≈-trans (prop._∧_.proj₁ e+) (+-cong (prop._∧_.proj₁ (ec-inj₁ {σ} {τ} i' s)) ≈-refl))) ,
  DepRel-resp σ r
    (λ k → +-cong (≈-sym (ctrl-lift-suc (ctrl-of v) s k)) ≈-refl)
    (F.sym σ i' (F.trans σ i' (prop._∧_.proj₂ e+)
                              (F.+-cong σ i' (prop._∧_.proj₂ (ec-inj₁ {σ} {τ} i' s)) (F.refl σ i'))))
    (ctrl-add σ r s h)
ctrl-add (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) s {o} {d} (h₀ , h) =
  let e+ = subst-ec+ (σ [+] τ) {i} {inj₂ i'} e s d
  in
  ≈-trans (+-cong (ctrl-lift-zero (ctrl-of v) s) h₀)
          (≈-sym (≈-trans (prop._∧_.proj₁ e+) (+-cong (prop._∧_.proj₁ (ec-inj₂ {σ} {τ} i' s)) ≈-refl))) ,
  DepRel-resp τ r
    (λ k → +-cong (≈-sym (ctrl-lift-suc (ctrl-of v) s k)) ≈-refl)
    (F.sym τ i' (F.trans τ i' (prop._∧_.proj₂ e+)
                              (F.+-cong τ i' (prop._∧_.proj₂ (ec-inj₂ {σ} {τ} i' s)) (F.refl τ i'))))
    (ctrl-add τ r s h)
ctrl-add (σ [×] τ) {pair v u} {i , j} (r , r') s {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans (+-cong (ctrl-lift-zero (⟨ ctrl-of v , ctrl-of u ⟩) s) h₀)
          (+-cong (≈-sym (prop._∧_.proj₁ (ec-pair {σ} {τ} i j s))) ≈-refl) ,
  (DepRel-resp σ r
     (λ k → ≈-trans (+-cong (≈-sym (ap-pair-p₁ (ctrl-of v) (ctrl-of u) (λ _ → s) k)) ≈-refl)
              (≈-trans (≈-sym (app-+ᵥ (M.p₁ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₁ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift-suc (⟨ ctrl-of v , ctrl-of u ⟩) s l)) ≈-refl) k)))
     (F.+-cong σ i (F.sym σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s)))) (F.refl σ i))
     (ctrl-add σ r s h₁) ,
   DepRel-resp τ r'
     (λ k → ≈-trans (+-cong (≈-sym (ap-pair-p₂ (ctrl-of v) (ctrl-of u) (λ _ → s) k)) ≈-refl)
              (≈-trans (≈-sym (app-+ᵥ (M.p₂ {width v} {width u}) _ _ k))
                       (app-congᵥ (M.p₂ {width v} {width u})
                          (λ l → +-cong (≈-sym (ctrl-lift-suc (⟨ ctrl-of v , ctrl-of u ⟩) s l)) ≈-refl) k)))
     (F.+-cong τ j (F.sym τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s)))) (F.refl τ j))
     (ctrl-add τ r' s h₂))
ctrl-add (σ [→] τ) {clo γ' t} {f} r s {o} {d} (h₀ , hc) =
  ≈-trans (+-cong (ctrl-lift-zero {width-env γ'} εₘ s) h₀)
          (+-cong (≈-sym (prop._∧_.proj₁ (ec-clo {σ} {τ} f s))) ≈-refl) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp τ (r rv D)
      (app-congᵥ U (body-input-resp γ' v
         (≈-trans +-assoc (+-cong ≈-refl (+-cong (≈-sym (ctrl-lift-zero {width-env γ'} εₘ s)) ≈-refl)))
         (λ k → ≈-sym (≈-trans (+-cong (ctrl-lift-suc {width-env γ'} εₘ s k) ≈-refl)
                               (≈-trans (+-cong (app-εₘ {width-env γ'} {1} (λ _ → s) k) ≈-refl) +-lunit)))))
      (F.+-cong τ (f .idxf .sfunc j)
         (elim-const τ .at (f .idxf .sfunc j) .SemiMod._⇒_.func-resp-≈
            (≈-trans +-assoc (+-cong ≈-refl (+-cong (≈-sym (ctrl-lift-zero {width-env γ'} εₘ s)) ≈-refl))))
         (F.+-cong τ (f .idxf .sfunc j)
            (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
               {proj₂ d} {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) d)}
               (P.sym {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) d)} {proj₂ d}
                 (P.trans {proj₂ (F._+_ (σ [→] τ) f (ec (σ [→] τ) f s) d)} {P._+_ P.ε (proj₂ d)} {proj₂ d}
                   (P.+-cong {proj₂ (ec (σ [→] τ) f s)} {P.ε} {proj₂ d} {proj₂ d}
                      (prop._∧_.proj₂ (ec-clo {σ} {τ} f s)) (P.refl {proj₂ d}))
                   (P.+-lunit {proj₂ d}))))
            (F.refl τ (f .idxf .sfunc j) {f .famf .transf j .func y})))
      (hc (s' +ₛ (w ·ₛ s)) rv z y hz D)
  where module P = Semimodule (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f)

-- Looking up a variable in a related environment.
lookup-val : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} → EnvValRel γ gi →
             ValRel τ (lookup x γ) (LI.⟦ x ⟧var .idxf .sfunc gi)
lookup-val zero     (rγ · r) = r
lookup-val (succ x) (rγ · r) = lookup-val x rγ

DepRel⊑-resp : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o o' : ∣ 𝔽 (width v) ∣} {d} →
               (∀ k → o k ≈s o' k) → DepRel⊑ τ r s o d → DepRel⊑ τ r s o' d
DepRel⊑-resp τ {i = i} r s eo (m , (dm , h)) = m , (dm , DepRel-resp τ r eo (F.refl τ i) h)

lookup-dep : ∀ {Γ τ} (x : Γ ∋ τ) {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s xs g →
             EnvDepRel rγ s xs g →
             DepRel⊑ τ (lookup-val x rγ) s (ap (proj-var x γ) xs) (LI.⟦ x ⟧var .famf .transf gi .func g)
lookup-dep zero (rγ · r) s xs g (_ , h) = h
lookup-dep {τ = τ} (succ x) {γ · v} {gi , i} (rγ · r) s xs g (h , _) =
  DepRel⊑-resp τ (lookup-val x rγ) s
    (λ k → ≈-sym (app-∘ (proj-var x γ) (M.p₁ {width-env γ} {width v}) xs k))
    (lookup-dep x rγ s (ap (M.p₁ {width-env γ} {width v}) xs) (proj₁ g) h)

-- Dependence below the constant is absorbed by it, so a relation up to such dependence becomes a
-- relation once the control positions and the constant are added.
⊑-absorb : ∀ τ (i : Ix τ) s (d m : ∣ Fib τ i ∣) → F._⊑_ τ i m (ec τ i s) →
         F._≈_ τ i (F._+_ τ i (ec τ i s) (F._+_ τ i d m)) (F._+_ τ i (ec τ i s) d)
⊑-absorb τ i s d m dm =
  F.trans τ i (F.+-cong τ i (F.refl τ i) (F.+-comm τ i))
  (F.trans τ i (F.sym τ i (F.+-assoc τ i))
  (F.trans τ i (F.+-cong τ i (F.trans τ i (F.+-comm τ i) dm) (F.refl τ i))
               (F.refl τ i)))

DepRel⊑-ctrl : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o : ∣ 𝔽 (width v) ∣} {d} →
               DepRel⊑ τ r s o d →
               DepRel τ r (λ k → ap (ctrl-of v) (λ _ → s) k +ₛ o k) (F._+_ τ i (ec τ i s) d)
DepRel⊑-ctrl τ {i = i} r s {o} {d} (m , (dm , h)) =
  DepRel-resp τ r (λ k → ≈-refl) (⊑-absorb τ i s d m dm) (ctrl-add τ r s h)

-- Related values are related at equal indices.
ValRel-resp : ∀ τ {v : Val τ} {i i' : Ix τ} → Setoid._≈_ (⟦ τ ⟧ .idx) i i' → ValRel τ v i → ValRel τ v i'
ValRel-resp unit {unit} e r = tt
ValRel-resp (base σ) {const c} {i} {i'} e ⟪ e₀ ⟫ =
  ⟪ Setoid.trans (sort-index σ) {i'} {i} {c} (Setoid.sym (sort-index σ) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [+] τ) {inl v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₁ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [+] τ) {inr v} {i} {i'} e (i₀ , r , ⟪ e₀ ⟫) =
  i₀ , r , ⟪ Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₂ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} e) e₀ ⟫
ValRel-resp (σ [×] τ) {pair v u} {i , j} {i' , j'} (e₁ , e₂) (r , r') = ValRel-resp σ e₁ r , ValRel-resp τ e₂ r'
ValRel-resp (σ [→] τ) {clo γ' t} {f} {f'} e r {v} {j} rv {u} {U} D =
  ValRel-resp τ (e .FD._≃_.idxf-eq .prop-setoid._≃m_.func-eq (Setoid.refl (⟦ σ ⟧ .idx) {j})) (r rv D)


-- Reading the model's constructions elementwise: a pairing through the biproduct is the pair of
-- the components, the lifted action keeps the root and acts on the payload, and eliminating a
-- root applies the continuation to the payload and the constant to the root.
module SMBP = HasProducts (cmon-enriched.biproducts→products SemiMod.cmon-enriched SemiMod.biproduct)

bpair-elt : ∀ {X Y Z : Semimodule} (f : X ⇒ Y) (g : X ⇒ Z) (x : ∣ X ∣) →
            Semimodule._≈_ (SemiMod._⊕_ Y Z) (SMBP.pair f g .func x) (f .func x , g .func x)
bpair-elt {X} {Y} {Z} f g x = m-runit Y , m-lunit Z

Fpair-elt : ∀ {X Y Z : Obj} (f : Mor X Y) (g : Mor X Z) (x : Setoid.Carrier (X .idx)) (z : ∣ X .fam .fm x ∣) →
            Semimodule._≈_ (HasProducts.prod FD.products Y Z .fam .fm (f .idxf .sfunc x , g .idxf .sfunc x))
              (HasProducts.pair FD.products f g .famf .transf x .func z)
              (f .famf .transf x .func z , g .famf .transf x .func z)
Fpair-elt f g x z = bpair-elt (f .famf .transf x) (g .famf .transf x) z

Lmap-elt : ∀ {X Y : Semimodule} (f : X ⇒ Y) (a : Setoid.Carrier A) (x : ∣ X ∣) →
           Semimodule._≈_ (Ls.L Y) (Ls.Lmap f .func (a , x)) (a , f .func x)
Lmap-elt {X} {Y} f a x = +-runit , m-lunit Y

elim-root-elt : ∀ {G X Y : Semimodule} (c : SemiMod.𝕀 ⇒ Y) (r : SemiMod._⊕_ G X ⇒ Y)
                (γe : ∣ G ∣) (a : Setoid.Carrier A) (y : ∣ X ∣) →
                Semimodule._≈_ Y (Ls.elim-root c r .func (γe , (a , y)))
                                 (Semimodule._+_ Y (r .func (γe , y)) (c .func a))
elim-root-elt {G} {X} {Y} c r γe a y =
  Semimodule.+-cong Y
    (r .SemiMod._⇒_.func-resp-≈
       (Semimodule.trans (SemiMod._⊕_ G X)
          (bpair-elt {SemiMod._⊕_ G (Ls.L X)} {G} {X}
             (SemiMod._∘_ (SemiMod.id G) (SemiMod.p₁ {G} {Ls.L X}))
             (SemiMod._∘_ (Ls.payload-L {X}) (SemiMod.p₂ {G} {Ls.L X})) (γe , (a , y)))
          (Semimodule.refl G {γe} , m-lunit X {y})))
    (c .SemiMod._⇒_.func-resp-≈ +-runit)

elimF-elt : ∀ {Γ' X C : Obj} (cC : Constant C) (f : Mor (HasProducts.prod FD.products Γ' X) C)
            {γi : Setoid.Carrier (Γ' .idx)} {xi : Setoid.Carrier (X .idx)}
            (γe : ∣ Γ' .fam .fm γi ∣) (a : Setoid.Carrier A) (y : ∣ X .fam .fm xi ∣) →
            Semimodule._≈_ (C .fam .fm (f .idxf .sfunc (γi , xi)))
              (FD.elimF cC f .famf .transf (γi , xi) .func (γe , (a , y)))
              (Semimodule._+_ (C .fam .fm (f .idxf .sfunc (γi , xi)))
                (f .famf .transf (γi , xi) .func (γe , y))
                (cC .at (f .idxf .sfunc (γi , xi)) .func a))
elimF-elt cC f {γi} {xi} γe a y = elim-root-elt (cC .at (f .idxf .sfunc (γi , xi))) (f .famf .transf (γi , xi)) γe a y

-- Being below the constant is monotone in the source weight, and a relation is a relation up to
-- zero.
ec-linear : ∀ τ (i : Ix τ) s s' →
            F._≈_ τ i (ec τ i (s +ₛ s')) (F._+_ τ i (ec τ i s) (ec τ i s'))
ec-linear τ i s s' = elim-const τ .at i .SemiMod._⇒_.preserve-+ {s} {s'}

ec-w : ∀ τ (i : Ix τ) s → F._≈_ τ i (ec τ i (w ·ₛ s)) (ec τ i s)
ec-w τ i s =
  LI.ty-unit τ (λ ()) (λ ()) .at i .SemiMod._⇒_.func-resp-≈
    (+-cong (≈-trans (≈-sym Sc.·-assoc) (·-cong w-idem ≈-refl)) ≈-refl)

⊑ec-mono : ∀ τ (i : Ix τ) s s' m → F._⊑_ τ i m (ec τ i s) → F._⊑_ τ i m (ec τ i (s' +ₛ (w ·ₛ s)))
⊑ec-mono τ i s s' m dm =
  F.trans τ i (F.+-cong τ i (F.refl τ i) (F.trans τ i (ec-linear τ i s' (w ·ₛ s))
                                                      (F.+-cong τ i (F.refl τ i) (ec-w τ i s))))
  (F.trans τ i (F.+-cong τ i (F.refl τ i) (F.+-comm τ i))
  (F.trans τ i (F.sym τ i (F.+-assoc τ i))
  (F.trans τ i (F.+-cong τ i dm (F.refl τ i))
  (F.trans τ i (F.+-comm τ i)
  (F.sym τ i (F.trans τ i (ec-linear τ i s' (w ·ₛ s))
                          (F.+-cong τ i (F.refl τ i) (ec-w τ i s))))))))

DepRel⊑-mono : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s s' {o d} →
               DepRel⊑ τ r s o d → DepRel⊑ τ r (s' +ₛ (w ·ₛ s)) o d
DepRel⊑-mono τ {i = i} r s s' (m , (dm , h)) = m , (⊑ec-mono τ i s s' m dm , h)

EnvDepRel-mono : ∀ {Γ} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s s' {x g} →
                 EnvDepRel rγ s x g → EnvDepRel rγ (s' +ₛ (w ·ₛ s)) x g
EnvDepRel-mono emp s s' rel = prop.tt
EnvDepRel-mono (rγ · r) s s' (rel , h) = EnvDepRel-mono rγ s s' rel , DepRel⊑-mono _ r s s' h

DepRel⊑-of : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {o d} → DepRel τ r o d → DepRel⊑ τ r s o d
DepRel⊑-of τ {i = i} r s {o} {d} h =
  F.ε τ i , (m-lunit (Fib τ i) , DepRel-resp τ r (λ k → ≈-refl) (F.sym τ i (m-runit (Fib τ i))) h)

-- Splitting a concatenated environment vector.
ap-p₁-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
           ap (M.p₁ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s x k
ap-p₁-++ {m} {n} x z k =
  ≈-trans (app-+ᵥ (M.p₁ {m} {n}) _ _ k)
          (≈-trans (+-cong (≈-trans (≈-sym (app-∘ (M.p₁ {m} {n}) (M.in₁ {m} {n}) x k))
                                    (≈-trans (app-congₘ (M.id-1 m n) x k) (app-I x k)))
                           (≈-trans (≈-sym (app-∘ (M.p₁ {m} {n}) (M.in₂ {m} {n}) z k))
                                    (≈-trans (app-congₘ (M.zero-1 m n) z k) (app-εₘ z k))))
                   +-runit)

ap-p₂-++ : ∀ {m n} (x : ∣ 𝔽 m ∣) (z : ∣ 𝔽 n ∣) k →
           ap (M.p₂ {m} {n}) (λ l → ap (M.in₁ {m} {n}) x l +ₛ ap (M.in₂ {m} {n}) z l) k ≈s z k
ap-p₂-++ {m} {n} x z k =
  ≈-trans (app-+ᵥ (M.p₂ {m} {n}) _ _ k)
          (≈-trans (+-cong (≈-trans (≈-sym (app-∘ (M.p₂ {m} {n}) (M.in₁ {m} {n}) x k))
                                    (≈-trans (app-congₘ (M.zero-2 m n) x k) (app-εₘ x k)))
                           (≈-trans (≈-sym (app-∘ (M.p₂ {m} {n}) (M.in₂ {m} {n}) z k))
                                    (≈-trans (app-congₘ (M.id-2 m n) z k) (app-I z k))))
                   +-lunit)

EnvDepRel-resp : ∀ {Γ} {γ : Env Γ} {gi} (rγ : EnvValRel γ gi) s {x x' g} →
                 (∀ k → x k ≈s x' k) → EnvDepRel rγ s x g → EnvDepRel rγ s x' g
EnvDepRel-resp emp s ex rel = prop.tt
EnvDepRel-resp (_·_ {γ = γ} {v = v} rγ r) s ex (rel , h) =
  EnvDepRel-resp rγ s (app-congᵥ (M.p₁ {width-env γ} {width v}) ex) rel ,
  DepRel⊑-resp _ r s (app-congᵥ (M.p₂ {width-env γ} {width v}) ex) h

-- Elements above the constant, and multiples of the source weight: an element is a multiple of
-- the source weight when it is that weight times the elimination weight times some element. A
-- relation to a sum with a multiple summand is a relation to the other summand when that summand is
-- above the constant in the additive order: at first-order types the constant absorbs the multiple
-- outright, and at arrow types the body's constant at the root does, since the root itself absorbs
-- the weighted source.
Multiple : ∀ τ (i : Ix τ) → Setoid.Carrier A → ∣ Fib τ i ∣ → Prop
Multiple τ i s E = ∃ (∣ Fib τ i ∣) (λ E' → F._≈_ τ i E (F._·_ τ i (s ·ₛ w) E'))

sw-absorb : ∀ s e → ((w ·ₛ s) +ₛ ((s ·ₛ w) ·ₛ e)) ≈s (w ·ₛ s)
sw-absorb s e =
  ≈-trans (+-cong ·-comm Sc.·-assoc)
  (≈-trans (≈-sym Sc.·-+-distribₗ)
  (≈-trans (·-cong ≈-refl (≈-trans +-comm (w-absorb e))) ·-comm))

-- A scalar absorbing the weight times the source absorbs any multiple of it.
root-absorb : ∀ s a e → (a +ₛ (w ·ₛ s)) ≈s a → (a +ₛ ((s ·ₛ w) ·ₛ e)) ≈s a
root-absorb s a e h =
  ≈-trans (+-cong (≈-sym h) ≈-refl) (≈-trans +-assoc (≈-trans (+-cong ≈-refl (sw-absorb s e)) h))

ec-root : ∀ τ (i : Ix τ) s → F._⊑_ τ i (ec τ i s) (ec τ i s)
ec-root τ i s = F.trans τ i (F.sym τ i (ec-linear τ i s s))
                            (elim-const τ .at i .SemiMod._⇒_.func-resp-≈ (+-idem s))

-- An element above the constant has a root absorbing the weight times the source and a payload
-- above the payload's constant.
ec⊑-inj₁ : ∀ {σ τ} (i : Ix σ) s (Q : ∣ Fib (σ [+] τ) (inj₁ i) ∣) →
           F._⊑_ (σ [+] τ) (inj₁ i) (ec (σ [+] τ) (inj₁ i) s) Q →
           ((proj₁ Q +ₛ (w ·ₛ s)) ≈s proj₁ Q) ∧ F._⊑_ σ i (ec σ i s) (proj₂ Q)
ec⊑-inj₁ {σ} {τ} i s Q (h₀ , h₁) =
  ≈-trans +-comm (≈-trans (+-cong (≈-sym (prop._∧_.proj₁ (ec-inj₁ {σ} {τ} i s))) ≈-refl) h₀) ,
  F.trans σ i (F.+-cong σ i (F.sym σ i (prop._∧_.proj₂ (ec-inj₁ {σ} {τ} i s))) (F.refl σ i)) h₁

ec⊑-inj₂ : ∀ {σ τ} (i : Ix τ) s (Q : ∣ Fib (σ [+] τ) (inj₂ i) ∣) →
           F._⊑_ (σ [+] τ) (inj₂ i) (ec (σ [+] τ) (inj₂ i) s) Q →
           ((proj₁ Q +ₛ (w ·ₛ s)) ≈s proj₁ Q) ∧ F._⊑_ τ i (ec τ i s) (proj₂ Q)
ec⊑-inj₂ {σ} {τ} i s Q (h₀ , h₁) =
  ≈-trans +-comm (≈-trans (+-cong (≈-sym (prop._∧_.proj₁ (ec-inj₂ {σ} {τ} i s))) ≈-refl) h₀) ,
  F.trans τ i (F.+-cong τ i (F.sym τ i (prop._∧_.proj₂ (ec-inj₂ {σ} {τ} i s))) (F.refl τ i)) h₁

ec⊑-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s Q → F._⊑_ (σ [×] τ) (i , j) (ec (σ [×] τ) (i , j) s) Q →
           ((proj₁ Q +ₛ (w ·ₛ s)) ≈s proj₁ Q) ∧
           (F._⊑_ σ i (ec σ i s) (proj₁ (proj₂ Q)) ∧ F._⊑_ τ j (ec τ j s) (proj₂ (proj₂ Q)))
ec⊑-pair {σ} {τ} i j s Q (h₀ , (h₁ , h₂)) =
  ≈-trans +-comm (≈-trans (+-cong (≈-sym (prop._∧_.proj₁ (ec-pair {σ} {τ} i j s))) ≈-refl) h₀) ,
  (F.trans σ i (F.+-cong σ i (F.sym σ i (prop._∧_.proj₁ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s)))) (F.refl σ i)) h₁ ,
   F.trans τ j (F.+-cong τ j (F.sym τ j (prop._∧_.proj₂ (prop._∧_.proj₂ (ec-pair {σ} {τ} i j s)))) (F.refl τ j)) h₂)

ec⊑-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s Q → F._⊑_ (σ [→] τ) f (ec (σ [→] τ) f s) Q →
          (proj₁ Q +ₛ (w ·ₛ s)) ≈s proj₁ Q
ec⊑-clo {σ} {τ} f s Q (h₀ , _) =
  ≈-trans +-comm (≈-trans (+-cong (≈-sym (prop._∧_.proj₁ (ec-clo {σ} {τ} f s))) ≈-refl) h₀)

-- Transport preserves being above the constant and being a multiple.
ec⊑-subst : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s Q → F._⊑_ τ i (ec τ i s) Q →
            F._⊑_ τ i' (ec τ i' s) (⟦ τ ⟧ .fam .subst e .func Q)
ec⊑-subst τ {i} {i'} e s Q h =
  F.trans τ i' (F.+-cong τ i' (F.sym τ i' (ec-natural τ e s)) (F.refl τ i'))
  (F.trans τ i' (F.sym τ i' (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.preserve-+ {ec τ i s} {Q}))
                (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.func-resp-≈ h))

multiple-subst : ∀ τ {i i' : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i') s E → Multiple τ i s E →
                Multiple τ i' s (⟦ τ ⟧ .fam .subst e .func E)
multiple-subst τ {i} {i'} e s E (E' , h) =
  ⟦ τ ⟧ .fam .subst e .func E' ,
  F.trans τ i' (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.func-resp-≈ h)
               (⟦ τ ⟧ .fam .subst e .SemiMod._⇒_.preserve-· {s ·ₛ w} {E'})

-- The root of a multiple is a multiple scalar; a lifted multiple has multiple parts.
root-of : ∀ s a b e → a ≈s (b +ₛ ((s ·ₛ w) ·ₛ e)) → (b +ₛ (w ·ₛ s)) ≈s b → a ≈s b
root-of s a b e ea hb = ≈-trans ea (root-absorb s b e hb)

ec⊑-ec : ∀ τ (i : Ix τ) s a → (a +ₛ (w ·ₛ s)) ≈s a → F._⊑_ τ i (ec τ i s) (ec τ i a)
ec⊑-ec τ i s a h =
  F.trans τ i (F.+-comm τ i)
    (F.sym τ i (F.trans τ i (elim-const τ .at i .SemiMod._⇒_.func-resp-≈ (≈-sym h))
                            (F.trans τ i (ec-linear τ i a (w ·ₛ s))
                                         (F.+-cong τ i (F.refl τ i) (ec-w τ i s)))))

-- The constant at the weighted source plus itself and a further weight: the constant at the
-- source plus the constant at the further weight.
ec-double : ∀ τ (i : Ix τ) s a → F._≈_ τ i (ec τ i ((w ·ₛ s) +ₛ ((w ·ₛ s) +ₛ a))) (F._+_ τ i (ec τ i s) (ec τ i a))
ec-double τ i s a =
  F.trans τ i (ec-linear τ i (w ·ₛ s) ((w ·ₛ s) +ₛ a))
  (F.trans τ i (F.+-cong τ i (ec-w τ i s) (F.trans τ i (ec-linear τ i (w ·ₛ s) a) (F.+-cong τ i (ec-w τ i s) (F.refl τ i))))
  (F.trans τ i (F.sym τ i (F.+-assoc τ i)) (F.+-cong τ i (ec-root τ i s) (F.refl τ i))))

ec-double' : ∀ τ (i : Ix τ) s a → F._≈_ τ i (ec τ i (((w ·ₛ s) +ₛ a) +ₛ (w ·ₛ s))) (F._+_ τ i (ec τ i s) (ec τ i a))
ec-double' τ i s a =
  F.trans τ i (elim-const τ .at i .SemiMod._⇒_.func-resp-≈ (≈-trans +-comm (≈-refl {(w ·ₛ s) +ₛ ((w ·ₛ s) +ₛ a)})))
              (ec-double τ i s a)

-- Splitting a bounded lifted element into a bounded root and a bounded payload.
MultipleA : Setoid.Carrier A → Setoid.Carrier A → Prop
MultipleA s a = ∃ (Setoid.Carrier A) (λ e → a ≈s ((s ·ₛ w) ·ₛ e))

multiple-inj₁ : ∀ {σ τ} (i : Ix σ) s E → Multiple (σ [+] τ) (inj₁ i) s E →
               MultipleA s (proj₁ E) ∧ Multiple σ i s (proj₂ E)
multiple-inj₁ i s E (E' , (h₀ , h₁)) = (proj₁ E' , h₀) , (proj₂ E' , h₁)

multiple-inj₂ : ∀ {σ τ} (i : Ix τ) s E → Multiple (σ [+] τ) (inj₂ i) s E →
               MultipleA s (proj₁ E) ∧ Multiple τ i s (proj₂ E)
multiple-inj₂ i s E (E' , (h₀ , h₁)) = (proj₁ E' , h₀) , (proj₂ E' , h₁)

multiple-pair : ∀ {σ τ} (i : Ix σ) (j : Ix τ) s E → Multiple (σ [×] τ) (i , j) s E →
               MultipleA s (proj₁ E) ∧ (Multiple σ i s (proj₁ (proj₂ E)) ∧ Multiple τ j s (proj₂ (proj₂ E)))
multiple-pair i j s E (E' , (h₀ , (h₁ , h₂))) = (proj₁ E' , h₀) , ((proj₁ (proj₂ E') , h₁) , (proj₂ (proj₂ E') , h₂))

multiple-clo : ∀ {σ τ} (f : Ix (σ [→] τ)) s E → Multiple (σ [→] τ) f s E →
              MultipleA s (proj₁ E) ∧
              ∃ (∣ model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f ∣)
                (λ E' → Semimodule._≈_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (proj₂ E)
                          (Semimodule._·_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (s ·ₛ w) E'))
multiple-clo f s E (E' , (h₀ , h₁)) = (proj₁ E' , h₀) , (proj₂ E' , h₁)

root-abs : ∀ s a b → MultipleA s a → (b +ₛ (w ·ₛ s)) ≈s b → (b +ₛ a) ≈s b
root-abs s a b (e , ea) hb = ≈-trans (+-cong ≈-refl ea) (root-absorb s b e hb)

DepRel-absorb : ∀ τ {v : Val τ} {i : Ix τ} (r : ValRel τ v i) s {P : ∣ 𝔽 (width v) ∣} {Q E : ∣ Fib τ i ∣} →
                DepRel τ r P (F._+_ τ i Q E) → F._⊑_ τ i (ec τ i s) Q → Multiple τ i s E → DepRel τ r P Q
DepRel-absorb unit {unit} {i} r s {P} {Q} {E} h hQ (E' , hE) zero =
  ≈-trans (h zero)
          (root-of s (Q zero +ₛ E zero) (Q zero) (E' zero) (+-cong ≈-refl (hE zero))
                   (≈-trans +-comm (≈-trans (+-cong (≈-sym (ec-unit i s)) ≈-refl) (hQ zero))))
DepRel-absorb (base σ) {const c} {i} r s {P} {Q} {E} h hQ (E' , hE) k =
  ≈-trans (h k)
          (root-of s (Q k +ₛ E k) (Q k) (E' k) (+-cong ≈-refl (hE k))
                   (≈-trans +-comm (≈-trans (+-cong (≈-sym (ec-base i s k)) ≈-refl) (hQ k))))
DepRel-absorb (σ [+] τ) {inl v} {i} (i' , r , ⟪ e ⟫) s {P} {Q} {E} (h₀ , h) hQ hE =
  let Q' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func Q
      E' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .func E
      split = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₁ i'} e .SemiMod._⇒_.preserve-+ {Q} {E}
      hQ' = ec⊑-inj₁ {σ} {τ} i' s Q' (ec⊑-subst (σ [+] τ) {i} {inj₁ i'} e s Q hQ)
      hE' = multiple-inj₁ {σ} {τ} i' s E' (multiple-subst (σ [+] τ) {i} {inj₁ i'} e s E hE)
  in
  ≈-trans h₀ (≈-trans (prop._∧_.proj₁ split) (root-abs s (proj₁ E') (proj₁ Q') (prop._∧_.proj₁ hE') (prop._∧_.proj₁ hQ'))) ,
  DepRel-absorb σ r s (DepRel-resp σ r (λ k → ≈-refl) (prop._∧_.proj₂ split) h) (prop._∧_.proj₂ hQ') (prop._∧_.proj₂ hE')
DepRel-absorb (σ [+] τ) {inr v} {i} (i' , r , ⟪ e ⟫) s {P} {Q} {E} (h₀ , h) hQ hE =
  let Q' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func Q
      E' = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .func E
      split = ⟦ σ [+] τ ⟧ .fam .subst {i} {inj₂ i'} e .SemiMod._⇒_.preserve-+ {Q} {E}
      hQ' = ec⊑-inj₂ {σ} {τ} i' s Q' (ec⊑-subst (σ [+] τ) {i} {inj₂ i'} e s Q hQ)
      hE' = multiple-inj₂ {σ} {τ} i' s E' (multiple-subst (σ [+] τ) {i} {inj₂ i'} e s E hE)
  in
  ≈-trans h₀ (≈-trans (prop._∧_.proj₁ split) (root-abs s (proj₁ E') (proj₁ Q') (prop._∧_.proj₁ hE') (prop._∧_.proj₁ hQ'))) ,
  DepRel-absorb τ r s (DepRel-resp τ r (λ k → ≈-refl) (prop._∧_.proj₂ split) h) (prop._∧_.proj₂ hQ') (prop._∧_.proj₂ hE')
DepRel-absorb (σ [×] τ) {pair v u} {i , j} (r , r') s {P} {Q} {E} (h₀ , (h₁ , h₂)) hQ hE =
  let hQ' = ec⊑-pair {σ} {τ} i j s Q hQ
      hE' = multiple-pair {σ} {τ} i j s E hE
  in
  ≈-trans h₀ (root-abs s (proj₁ E) (proj₁ Q) (prop._∧_.proj₁ hE') (prop._∧_.proj₁ hQ')) ,
  (DepRel-absorb σ r s h₁ (prop._∧_.proj₁ (prop._∧_.proj₂ hQ')) (prop._∧_.proj₁ (prop._∧_.proj₂ hE')) ,
   DepRel-absorb τ r' s h₂ (prop._∧_.proj₂ (prop._∧_.proj₂ hQ')) (prop._∧_.proj₂ (prop._∧_.proj₂ hE')))
DepRel-absorb (σ [→] τ) {clo γ' t} {f} r s {P} {Q} {E} (h₀ , hc) hQ hE =
  root ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-absorb τ (r rv D) s
      (DepRel-resp τ (r rv D) (λ k → ≈-refl)
         (F.trans τ (f .idxf .sfunc j)
            (F.+-cong τ (f .idxf .sfunc j) (F.refl τ (f .idxf .sfunc j))
               (F.+-cong τ (f .idxf .sfunc j)
                  (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.preserve-+ {proj₂ Q} {proj₂ E})
                  (F.refl τ (f .idxf .sfunc j))))
            (F.trans τ (f .idxf .sfunc j) (F.+-cong τ (f .idxf .sfunc j) (F.refl τ (f .idxf .sfunc j)) (F.+-assoc τ (f .idxf .sfunc j)))
            (F.trans τ (f .idxf .sfunc j) (F.+-cong τ (f .idxf .sfunc j) (F.refl τ (f .idxf .sfunc j))
                                             (F.+-cong τ (f .idxf .sfunc j) (F.refl τ (f .idxf .sfunc j)) (F.+-comm τ (f .idxf .sfunc j))))
            (F.trans τ (f .idxf .sfunc j) (F.+-cong τ (f .idxf .sfunc j) (F.refl τ (f .idxf .sfunc j)) (F.sym τ (f .idxf .sfunc j) (F.+-assoc τ (f .idxf .sfunc j))))
                     (F.sym τ (f .idxf .sfunc j) (F.+-assoc τ (f .idxf .sfunc j)))))))
         (hc s' rv z y hz D))
      (absQ₁ s' {j} {y})
      (bndE₁ {j} (prop._∧_.proj₂ hE'))
  where
  hE' = multiple-clo {σ} {τ} f s E hE
  root : P zero ≈A proj₁ Q
  root = ≈-trans h₀ (root-abs s (proj₁ E) (proj₁ Q) (prop._∧_.proj₁ hE') (ec⊑-clo {σ} {τ} f s Q hQ))
  P₀-abs : (P zero +ₛ (w ·ₛ s)) ≈s P zero
  P₀-abs = ≈-trans (+-cong root ≈-refl) (≈-trans (ec⊑-clo {σ} {τ} f s Q hQ) (≈-sym root))
  absQ₁ : ∀ s' {j : Ix σ} {y : ∣ Fib σ j ∣} →
          F._⊑_ τ (f .idxf .sfunc j) (ec τ (f .idxf .sfunc j) s)
            (F._+_ τ (f .idxf .sfunc j) (ec τ (f .idxf .sfunc j) (s' +ₛ P zero))
              (F._+_ τ (f .idxf .sfunc j) (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ Q))
                                           (f .famf .transf j .func y)))
  absQ₁ s' {j} {y} =
    F.trans τ i₁ (F.sym τ i₁ (F.+-assoc τ i₁))
      (F.+-cong τ i₁ (ec⊑-ec τ i₁ s (s' +ₛ P zero) (≈-trans +-assoc (+-cong ≈-refl P₀-abs))) (F.refl τ i₁))
    where i₁ = f .idxf .sfunc j
  bndE₁ : ∀ {j : Ix σ} →
          ∃ (∣ model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f ∣)
            (λ E' → Semimodule._≈_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (proj₂ E)
                      (Semimodule._·_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (s ·ₛ w) E')) →
          Multiple τ (f .idxf .sfunc j) s (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ E))
  bndE₁ {j} (E' , h) =
    SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func E' ,
    F.trans τ (f .idxf .sfunc j)
      (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.func-resp-≈
         {proj₂ E} {Semimodule._·_ (model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧ .fam .fm f) (s ·ₛ w) E'} h)
      (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .SemiMod._⇒_.preserve-· {s ·ₛ w} {E'})

-- Reading the first position of a lifted vector, and its tail, by the projections.
built-zero : ∀ {Γ} {γ : Env Γ} {n} (R' : M.Matrix n (suc (width-env γ))) s x →
             ap (built-out γ n +ₘ (M.in₂ {1} ∘ R')) (inputs γ s x) zero ≈s (w ·ₛ s)
built-zero {γ = γ} {n} R' s x =
  ≈-trans (app-+ₘ (built-out γ n) (M.in₂ {1} ∘ R') (inputs γ s x) zero)
  (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) wsrc (inputs γ s x) zero)
                            (≈-trans (ap-in₁-zero {n} (ap wsrc (inputs γ s x)))
                                     (ap-wsrc {width-env γ} {1} (inputs γ s x) zero)))
                   (≈-trans (app-∘ (M.in₂ {1} {n}) R' (inputs γ s x) zero)
                            (ap-in₂-zero {n} (ap R' (inputs γ s x)))))
           +-runit)

built-suc : ∀ {Γ} {γ : Env Γ} {n} (R' : M.Matrix n (suc (width-env γ))) s x k →
            ap (built-out γ n +ₘ (M.in₂ {1} ∘ R')) (inputs γ s x) (suc k) ≈s ap R' (inputs γ s x) k
built-suc {γ = γ} {n} R' s x k =
  ≈-trans (app-+ₘ (built-out γ n) (M.in₂ {1} ∘ R') (inputs γ s x) (suc k))
  (≈-trans (+-cong (≈-trans (app-∘ (M.in₁ {1} {n}) wsrc (inputs γ s x) (suc k))
                            (ap-in₁-suc {n} (ap wsrc (inputs γ s x)) k))
                   (≈-trans (app-∘ (M.in₂ {1} {n}) R' (inputs γ s x) (suc k))
                            (ap-in₂-suc {n} (ap R' (inputs γ s x)) k)))
           +-lunit)

-- Transport along a reflexivity proof is the identity.
subst-refl : ∀ τ {i : Ix τ} (e : Setoid._≈_ (⟦ τ ⟧ .idx) i i) (d : ∣ Fib τ i ∣) →
             F._≈_ τ i (⟦ τ ⟧ .fam .subst e .func d) d
subst-refl τ {i} e d = ⟦ τ ⟧ .fam .indexed-family.Fam.refl* .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl τ i {d})

-- A base sort's fibres do not vary with the index, so its transports are the identity.
subst-base : ∀ {σ} {i i' : Ix (base σ)} (e : Setoid._≈_ (⟦ base σ ⟧ .idx) i i')
             (d : ∣ Fib (base σ) i ∣) (k : Fin (sort-width σ)) →
             ⟦ base σ ⟧ .fam .subst e .func d k ≈s d k
subst-base {σ} e d k = Σ-unit {sort-width σ} k d

-- Transporting a relation along an index equation.
DepRel-transport : ∀ τ {v : Val τ} {i i' : Ix τ} (E : Setoid._≈_ (⟦ τ ⟧ .idx) i i') (r : ValRel τ v i)
                   {o : ∣ 𝔽 (width v) ∣} {d : ∣ Fib τ i ∣} →
                   DepRel τ r o d → DepRel τ (ValRel-resp τ E r) o (⟦ τ ⟧ .fam .subst E .func d)
DepRel-transport unit {unit} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-refl unit {i} E d k))
DepRel-transport (base σ) {const c} {i} {i'} E r {o} {d} h k =
  ≈-trans (h k) (≈-sym (subst-base {σ} {i} {i'} E d k))
DepRel-transport (σ [+] τ) {inl v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₁ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} E) e₀
      comp = ⟦ σ [+] τ ⟧ .fam .indexed-family.Fam.trans* {i} {i'} {inj₁ i₀} e' E
               .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl (σ [+] τ) i {d})
  in
  ≈-trans h₀ (prop._∧_.proj₁ comp) ,
  DepRel-resp σ r₀ (λ k → ≈-refl) (prop._∧_.proj₂ comp) h
DepRel-transport (σ [+] τ) {inr v} {i} {i'} E (i₀ , r₀ , ⟪ e₀ ⟫) {o} {d} (h₀ , h) =
  let e' = Setoid.trans (⟦ σ [+] τ ⟧ .idx) {i'} {i} {inj₂ i₀} (Setoid.sym (⟦ σ [+] τ ⟧ .idx) {i} {i'} E) e₀
      comp = ⟦ σ [+] τ ⟧ .fam .indexed-family.Fam.trans* {i} {i'} {inj₂ i₀} e' E
               .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq (F.refl (σ [+] τ) i {d})
  in
  ≈-trans h₀ (prop._∧_.proj₁ comp) ,
  DepRel-resp τ r₀ (λ k → ≈-refl) (prop._∧_.proj₂ comp) h
DepRel-transport (σ [×] τ) {pair v u} {i , j} {i' , j'} (E₁ , E₂) (r₁ , r₂) {o} {d} (h₀ , (h₁ , h₂)) =
  ≈-trans h₀ (≈-sym +-runit) ,
  (DepRel-resp σ (ValRel-resp σ E₁ r₁) (λ k → ≈-refl)
     (F.sym σ i' (F.trans σ i' (m-lunit (Fib σ i')) (m-runit (Fib σ i'))))
     (DepRel-transport σ E₁ r₁ h₁) ,
   DepRel-resp τ (ValRel-resp τ E₂ r₂) (λ k → ≈-refl)
     (F.sym τ j' (F.trans τ j' (m-lunit (Fib τ j')) (m-lunit (Fib τ j'))))
     (DepRel-transport τ E₂ r₂ h₂))
DepRel-transport (σ [→] τ) {clo γ' t} {f} {f'} E r {o} {d} (h₀ , hc) =
  ≈-trans h₀ (≈-sym +-runit) ,
  λ s' {v} {j} rv z y hz {u} {U} D →
    DepRel-resp τ (ValRel-resp τ (Ej j) (r rv D)) (λ k → ≈-refl)
      (F.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .SemiMod._⇒_.preserve-+ {ec τ (f .idxf .sfunc j) (s' +ₛ o zero)} {_})
      (F.+-cong τ (f' .idxf .sfunc j) (ec-natural τ (Ej j) (s' +ₛ o zero))
      (F.trans τ (f' .idxf .sfunc j)
         (⟦ τ ⟧ .fam .subst (Ej j) .SemiMod._⇒_.preserve-+ {_} {_})
      (F.+-cong τ (f' .idxf .sfunc j) (eval-part j) (arg-part j y)))))
      (DepRel-transport τ (Ej j) (r rv D) (hc s' rv z y hz D))
  where
  P = model.FE._⟶_ ⟦ σ ⟧ ⟦ τ ⟧
  Ej : ∀ j → Setoid._≈_ (⟦ τ ⟧ .idx) (f .idxf .sfunc j) (f' .idxf .sfunc j)
  Ej j = E .FD._≃_.idxf-eq .prop-setoid._≃m_.func-eq (Setoid.refl (⟦ σ ⟧ .idx) {j})
  hmap = indexed-family.reindex-≈ {P = ⟦ τ ⟧ .fam} (f .idxf) (f' .idxf) (E .FD._≃_.idxf-eq)
  eval-part : ∀ j → F._≈_ τ (f' .idxf .sfunc j)
                (⟦ τ ⟧ .fam .subst (Ej j) .func (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]) j .func (proj₂ d)))
                (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]) j .func
                   (proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)))
  eval-part j =
    F.trans τ (f' .idxf .sfunc j)
      (F.sym τ (f' .idxf .sfunc j)
         (SP.lambda-eval {A = ⟦ σ ⟧ .idx} {P = ⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]}
            {x = P .fam .fm f}
            {f = indexed-family._∘f_ {A = ⟦ σ ⟧ .idx}
                   {P = indexed-family.constantFam (⟦ σ ⟧ .idx) SemiMod.cat (P .fam .fm f)}
                   {Q = ⟦ τ ⟧ .fam indexed-family.[ f .idxf ]} {R = ⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]}
                   hmap (SP.evalΠf {A = ⟦ σ ⟧ .idx} (⟦ τ ⟧ .fam indexed-family.[ f .idxf ]))} j
            .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq {proj₂ d} {proj₂ d} (Semimodule.refl (P .fam .fm f) {proj₂ d})))
      (SP.evalΠ (⟦ τ ⟧ .fam indexed-family.[ f' .idxf ]) j .SemiMod._⇒_.func-resp-≈
         {SP.Π-map hmap .func (proj₂ d)} {proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)}
         (Semimodule.sym (P .fam .fm f') {proj₂ (⟦ σ [→] τ ⟧ .fam .subst {f} {f'} E .func d)} {SP.Π-map hmap .func (proj₂ d)}
            (m-lunit (P .fam .fm f') {SP.Π-map hmap .func (proj₂ d)})))
  arg-part : ∀ j (y : ∣ Fib σ j ∣) →
             F._≈_ τ (f' .idxf .sfunc j) (⟦ τ ⟧ .fam .subst (Ej j) .func (f .famf .transf j .func y))
                                        (f' .famf .transf j .func y)
  arg-part j y = E .FD._≃_.famf-eq .indexed-family._≃f_.transf-eq {j} .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq
                   (Semimodule.refl (Fib σ j) {y})

