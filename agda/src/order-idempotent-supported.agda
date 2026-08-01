{-# OPTIONS --prop --postfix-projections --safe #-}

-- The supported realisation of a position order: the semimodule of its fixed vectors, with the join
-- of the coordinates as the support. Realising a lifted order gives the lift of the realisation:
-- a fixed vector of Lp P is exactly a scalar dominating a fixed tail, which is an element of the
-- supported lift. This is the object-level comparison between the lifting on position orders and
-- the lifting on supported semimodules.
open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; _×_)
open import prop using (_∧_; ∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; HasTerminal; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproduct-iso)
open import functor using (Functor)
import matrix
import semimodule
import order-idempotent
import order-idempotent-support
import order-idempotent-freeness
import supported-semimod

module order-idempotent-supported
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module S = CommutativeSemiring S)
  (∨-idem    : ∀ {x} → (x S.+ x) S.≈ x)
  (∧-idem    : ∀ {x} → (x S.· x) S.≈ x)
  (⊤-add-top : ∀ {x} → (S.ι S.+ x) S.≈ S.ι)
  where

module M = matrix.Mat S
module OI = order-idempotent S ∨-idem ∧-idem ⊤-add-top
module OS = order-idempotent-support S ∨-idem ∧-idem ⊤-add-top
module OF = order-idempotent-freeness S ∨-idem ∧-idem ⊤-add-top
module SemiMod = semimodule S
module SS = supported-semimod S ∨-idem

open OI using (Pos; dim; ord; Lp)
open SemiMod using (Semimodule; 𝕀; _⇒_)
open Semimodule
open SemiMod._⇒_
open SemiMod._≈m_

-- The action of a matrix is linear in the vector.
app-+ : ∀ {m n} (R : M.Matrix m n) (u v : M.Vec n) (i : Fin m) →
        OS.app R (λ j → u j S.+ v j) i S.≈ (OS.app R u i S.+ OS.app R v i)
app-+ {m} {n} R u v i =
  S.trans (M.Σ-cong {n} (λ j → S.·-+-distribₗ))
          (S.sym (M.Σ-+ {n} (λ j → R i j S.· u j) (λ j → R i j S.· v j)))

app-· : ∀ {m n} (R : M.Matrix m n) (s : S.Carrier) (u : M.Vec n) (i : Fin m) →
        OS.app R (λ j → s S.· u j) i S.≈ (s S.· OS.app R u i)
app-· {m} {n} R s u i =
  S.trans (M.Σ-cong {n} (λ j → S.trans (S.sym S.·-assoc)
                               (S.trans (S.·-cong S.·-comm S.refl) S.·-assoc)))
          (S.sym (M.Σ-·-distribₗ {n} s (λ j → R i j S.· u j)))

app-ε : ∀ {m n} (R : M.Matrix m n) (i : Fin m) → OS.app R (λ _ → S.ε) i S.≈ S.ε
app-ε {m} {n} R i = S.trans (M.Σ-cong {n} (λ j → S.ε-annihilᵣ)) (M.Σ-ε {n})

-- The semimodule of fixed vectors: the down-closed selections, pointwise.
𝓥sm : Pos → Semimodule
𝓥sm P .setoid .Setoid.Carrier = ∃ₛ (M.Vec (P .dim)) (OS.Fixed P)
𝓥sm P .setoid .Setoid._≈_ (u ,ₚ _) (v ,ₚ _) = ∀ i → u i S.≈ v i
𝓥sm P .setoid .Setoid.isEquivalence .IsEquivalence.refl i = S.refl
𝓥sm P .setoid .Setoid.isEquivalence .IsEquivalence.sym e i = S.sym (e i)
𝓥sm P .setoid .Setoid.isEquivalence .IsEquivalence.trans e e' i = S.trans (e i) (e' i)
𝓥sm P .additive .CommutativeMonoid.ε = (λ _ → S.ε) ,ₚ λ i → app-ε (P .ord) i
𝓥sm P .additive .CommutativeMonoid._+_ (u ,ₚ p) (v ,ₚ q) =
  (λ i → u i S.+ v i) ,ₚ λ i → S.trans (app-+ (P .ord) u v i) (S.+-cong (p i) (q i))
𝓥sm P .additive .CommutativeMonoid.+-cong e e' i = S.+-cong (e i) (e' i)
𝓥sm P .additive .CommutativeMonoid.+-lunit i = S.+-lunit
𝓥sm P .additive .CommutativeMonoid.+-assoc i = S.+-assoc
𝓥sm P .additive .CommutativeMonoid.+-comm i = S.+-comm
𝓥sm P ._·_ s (u ,ₚ p) =
  (λ i → s S.· u i) ,ₚ λ i → S.trans (app-· (P .ord) s u i) (S.·-cong S.refl (p i))
𝓥sm P .·-cong e e' i = S.·-cong e (e' i)
𝓥sm P .·-mul i = S.·-assoc
𝓥sm P .·-unit i = S.·-lunit
𝓥sm P .+-distribʳ i = S.·-+-distribᵣ
𝓥sm P .+-distribˡ i = S.·-+-distribₗ
𝓥sm P .zero-distribʳ i = S.ε-annihilₗ
𝓥sm P .zero-distribˡ i = S.ε-annihilᵣ

supp-𝓥 : ∀ P → 𝓥sm P ⇒ 𝕀
supp-𝓥 P .*→* .prop-setoid._⇒_.func (u ,ₚ _) = OS.supp {P .dim} u
supp-𝓥 P .*→* .prop-setoid._⇒_.func-resp-≈ e = M.Σ-cong e
supp-𝓥 P .preserve-ze = M.Σ-ε {P .dim}
supp-𝓥 P .preserve-+ {u ,ₚ _} {v ,ₚ _} = S.sym (M.Σ-+ {P .dim} u v)
supp-𝓥 P .preserve-· {s} {u ,ₚ _} = S.sym (M.Σ-·-distribₗ {P .dim} s u)

-- The supported object of a position order.
𝓥 : Pos → SS.Sup.Obj
𝓥 P .SS.Sup.carrier = 𝓥sm P
𝓥 P .SS.Sup.supp = supp-𝓥 P

private
  cons : ∀ {n} → S.Carrier → M.Vec n → M.Vec (suc n)
  cons a u zero    = a
  cons a u (suc i) = u i

-- Realising a lifted order is lifting the realisation: head and tail against pairing.
𝓥-Lp-fwd : ∀ P → SS.Sup.Mor (𝓥 (Lp P)) (SS.Ls (𝓥 P))
𝓥-Lp-fwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func (v ,ₚ fx) =
  (v zero , (OS.tail v ,ₚ OS.Lp-fixed-tail P v fx)) ,ₚ OS.Lp-fixed-root P v fx
𝓥-Lp-fwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ e = e zero ,ₚ λ i → e (suc i)
𝓥-Lp-fwd P .SS.Sup.mor .preserve-ze = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.mor .preserve-+ = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.mor .preserve-· = S.refl ,ₚ λ i → S.refl
𝓥-Lp-fwd P .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  S.trans (OI.L.Σ-ub v₁ zero) (M.Σ-cong e)

𝓥-Lp-bwd : ∀ P → SS.Sup.Mor (SS.Ls (𝓥 P)) (𝓥 (Lp P))
𝓥-Lp-bwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func ((a , (u ,ₚ fu)) ,ₚ dom) =
  cons a u ,ₚ OS.Lp-fixed P (cons a u) fu dom
𝓥-Lp-bwd P .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ (e₁ ,ₚ e₂) = λ where
  zero    → e₁
  (suc i) → e₂ i
𝓥-Lp-bwd P .SS.Sup.mor .preserve-ze = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.mor .preserve-+ = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.mor .preserve-· = λ where
  zero    → S.refl
  (suc i) → S.refl
𝓥-Lp-bwd P .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq
    {(a₁ , (u₁ ,ₚ _)) ,ₚ _} {(a₂ , (u₂ ,ₚ _)) ,ₚ dom₂} (e₁ ,ₚ e₂) =
  S.trans S.+-comm
  (S.trans (S.sym S.+-assoc)
  (S.trans (S.+-cong ∨-idem S.refl)
  (S.trans S.+-comm
  (S.trans (S.+-cong (M.Σ-cong e₂) e₁) dom₂))))

𝓥-Lp-iso : ∀ P → Category.Iso SS.Sup.cat (𝓥 (Lp P)) (SS.Ls (𝓥 P))
𝓥-Lp-iso P .Category.Iso.fwd = 𝓥-Lp-fwd P
𝓥-Lp-iso P .Category.Iso.bwd = 𝓥-Lp-bwd P
𝓥-Lp-iso P .Category.Iso.fwd∘bwd≈id .*≈* .prop-setoid._≃m_.func-eq e = e
𝓥-Lp-iso P .Category.Iso.bwd∘fwd≈id .*≈* .prop-setoid._≃m_.func-eq e = λ where
  zero    → e zero
  (suc i) → e (suc i)

-- The action of a position-order morphism on fixed vectors, which no morphism unfixes since the
-- target order is absorbed.
app-congₘ : ∀ {m n} {R R' : M.Matrix m n} → R M.≈ₘ R' →
            ∀ (v : M.Vec n) (i : Fin m) → OS.app R v i S.≈ OS.app R' v i
app-congₘ {m} {n} h v i = M.Σ-cong {n} (λ j → S.·-cong (h i j) S.refl)

app-∘ : ∀ {m n k} (R : M.Matrix m n) (T : M.Matrix n k) (v : M.Vec k) (i : Fin m) →
        OS.app (R M.∘ T) v i S.≈ OS.app R (OS.app T v) i
app-∘ {m} {n} {k} R T v i =
  S.trans (M.Σ-cong {k} (λ j → M.Σ-·-distribᵣ (λ l → R i l S.· T l j) (v j)))
  (S.trans (M.Σ-cong {k} (λ j → M.Σ-cong {n} (λ l → S.·-assoc)))
  (S.trans (M.Σ-interchange {k} {n} (λ j l → R i l S.· (T l j S.· v j)))
           (M.Σ-cong {n} (λ l → S.sym (M.Σ-·-distribₗ (R i l) (λ j → T l j S.· v j))))))

𝓥₁ : ∀ {P Q} → P OI.⇒ Q → SS.Sup.Mor (𝓥 P) (𝓥 Q)
𝓥₁ {P} {Q} f .SS.Sup.mor .*→* .prop-setoid._⇒_.func (v ,ₚ fx) =
  OS.app (f .OI.mat) v ,ₚ λ i →
    S.trans (S.sym (app-∘ (Q .ord) (f .OI.mat) v i)) (app-congₘ (OI.absorb-left f) v i)
𝓥₁ {P} {Q} f .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ e i =
  M.Σ-cong {P .dim} (λ j → S.·-cong S.refl (e j))
𝓥₁ {P} {Q} f .SS.Sup.mor .preserve-ze i = app-ε (f .OI.mat) i
𝓥₁ {P} {Q} f .SS.Sup.mor .preserve-+ {u ,ₚ _} {v ,ₚ _} i = app-+ (f .OI.mat) u v i
𝓥₁ {P} {Q} f .SS.Sup.mor .preserve-· {s'} {u ,ₚ _} i = app-· (f .OI.mat) s' u i
𝓥₁ {P} {Q} f .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  S.trans (OS.mor-supp f v₁) (M.Σ-cong e)

-- The one-position order realises as the scalars.
ι1-fwd : SS.Sup.Mor (𝓥 OF.𝟙p) SS.𝟙s
ι1-fwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func (v ,ₚ _) = v zero
ι1-fwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ e = e zero
ι1-fwd .SS.Sup.mor .preserve-ze = S.refl
ι1-fwd .SS.Sup.mor .preserve-+ = S.refl
ι1-fwd .SS.Sup.mor .preserve-· = S.refl
ι1-fwd .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  S.trans (S.sym S.+-assoc)
          (S.trans (S.+-cong ∨-idem S.refl) (S.+-cong (e zero) S.refl))

ι1-bwd : SS.Sup.Mor SS.𝟙s (𝓥 OF.𝟙p)
ι1-bwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func s = (λ _ → s) ,ₚ λ i → M.Σ-unit i (λ _ → s)
ι1-bwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ e i = e
ι1-bwd .SS.Sup.mor .preserve-ze i = S.refl
ι1-bwd .SS.Sup.mor .preserve-+ i = S.refl
ι1-bwd .SS.Sup.mor .preserve-· i = S.refl
ι1-bwd .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq e =
  S.trans (S.+-cong (S.trans (S.+-cong S.refl (M.Σ-ε {0})) (S.trans S.+-comm S.+-lunit)) S.refl)
          (S.trans ∨-idem e)

private
  module SC = Category SS.Sup.cat

-- The comparison intertwines the two liftings: the root, the injection and the assembly on
-- position orders realise as those of the supported lift.
root-intertwine : ∀ P →
  SC._≈_ (SC._∘_ (𝓥-Lp-iso P .Category.Iso.fwd) (𝓥₁ (OF.root {P})))
         (SC._∘_ (SS.root-s {𝓥 P}) ι1-fwd)
root-intertwine P .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e =
  S.trans (S.+-cong S.·-lunit (M.Σ-ε {0}))
          (S.trans S.+-comm (S.trans S.+-lunit (e zero)))
  ,ₚ λ i → S.trans (S.+-cong S.ε-annihilₗ (M.Σ-ε {0})) S.+-lunit

inj-intertwine : ∀ P →
  SC._≈_ (SC._∘_ (𝓥-Lp-iso P .Category.Iso.fwd) (𝓥₁ (OF.inj {P})))
         (SS.inj-s {𝓥 P})
inj-intertwine P .*≈* .prop-setoid._≃m_.func-eq {u₁ ,ₚ fu₁} {u₂ ,ₚ _} e =
  S.trans (M.Σ-cong {P .dim} (λ j → S.·-lunit)) (M.Σ-cong e)
  ,ₚ λ i → S.trans (fu₁ i) (e i)

affine-intertwine : ∀ {P C} (c : OF.𝟙p OI.⇒ C) (Mm : P OI.⇒ C) →
  SC._≈_ (SC._∘_ (𝓥₁ (OF.affine {P} {C} c Mm)) (𝓥-Lp-iso P .Category.Iso.bwd))
         (SS.affine-s (SC._∘_ (𝓥₁ c) ι1-bwd) (𝓥₁ Mm))
affine-intertwine {P} {C} c Mm .*≈* .prop-setoid._≃m_.func-eq
    {(a₁ , (u₁ ,ₚ _)) ,ₚ d₁} {(a₂ , (u₂ ,ₚ _)) ,ₚ _} (e₁ ,ₚ e₂) q =
  S.trans (S.+-cong S.refl (M.Σ-cong {P .dim} (λ p → S.·-+-distribᵣ)))
  (S.trans (S.+-cong S.refl (S.sym (M.Σ-+ {P .dim} (λ p → c .OI.mat q zero S.· u₁ p)
                                                    (λ p → Mm .OI.mat q p S.· u₁ p))))
  (S.trans (S.+-cong S.refl (S.+-cong (S.sym (M.Σ-·-distribₗ (c .OI.mat q zero) u₁)) S.refl))
  (S.trans (S.sym S.+-assoc)
  (S.trans (S.+-cong (S.sym S.·-+-distribₗ) S.refl)
  (S.trans (S.+-cong (S.·-cong S.refl (S.trans S.+-comm d₁)) S.refl)
  (S.trans (S.+-cong (S.·-cong S.refl e₁)
                     (M.Σ-cong {P .dim} (λ j → S.·-cong S.refl (e₂ j))))
           (S.+-cong (S.sym (S.trans S.+-comm S.+-lunit)) S.refl)))))))

-- The realisation packaged as a functor: identities act as the order, which fixes exactly the
-- realised vectors, and composition is composition of matrix actions.
𝓥F : Functor OI.cat SS.Sup.cat
𝓥F .Functor.fobj = 𝓥
𝓥F .Functor.fmor = 𝓥₁
𝓥F .Functor.fmor-cong {P} {Q} {f} {g} h .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e i =
  M.Σ-cong {P .dim} (λ j → S.·-cong (h i j) (e j))
𝓥F .Functor.fmor-id {P} .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ fx₁} {v₂ ,ₚ _} e i =
  S.trans (fx₁ i) (e i)
𝓥F .Functor.fmor-comp {P} {Q} {R} f g .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e i =
  S.trans (app-∘ (f .OI.mat) (g .OI.mat) v₁ i)
          (M.Σ-cong {Q .dim} (λ j → S.·-cong S.refl
            (M.Σ-cong {P .dim} (λ k → S.·-cong S.refl (e k)))))

-- The down-closure of a basis vector is fixed, and morphisms are determined by their action on
-- those closures, since absorption reads the matrix back off them.
colv : ∀ (P : Pos) (p : Fin (P .dim)) → ∃ₛ (M.Vec (P .dim)) (OS.Fixed P)
colv P p = (λ i → P .ord i p) ,ₚ λ i → OI.ord-idem P i p

𝓥-faithful : ∀ {P Q} {f g : P OI.⇒ Q} → SC._≈_ (𝓥₁ f) (𝓥₁ g) → OI._≈p_ f g
𝓥-faithful {P} {Q} {f} {g} h q p =
  S.trans (S.sym (OI.absorb-right f q p))
  (S.trans (h .*≈* .prop-setoid._≃m_.func-eq {colv P p} {colv P p} (λ i → S.refl) q)
           (OI.absorb-right g q p))

-- The empty order realises as the terminal supported object.
Sup-terminal : HasTerminal SS.Sup.cat
Sup-terminal = SS.Sup.terminal-s SemiMod.terminal

private
  module MC = Category SemiMod.cat
  T𝟘 = SemiMod.terminal .HasTerminal.witness
  to-T : ∀ (X : Semimodule) → X ⇒ T𝟘
  to-T X = SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal {X}

𝓥-𝟘-fwd : SS.Sup.Mor (𝓥 OI.𝟘p) (Sup-terminal .HasTerminal.witness)
𝓥-𝟘-fwd .SS.Sup.mor = to-T (𝓥sm OI.𝟘p)
𝓥-𝟘-fwd .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq e = S.+-lunit

𝓥-𝟘-bwd : SS.Sup.Mor (Sup-terminal .HasTerminal.witness) (𝓥 OI.𝟘p)
𝓥-𝟘-bwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func _ = (λ ()) ,ₚ λ ()
𝓥-𝟘-bwd .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ _ = λ ()
𝓥-𝟘-bwd .SS.Sup.mor .preserve-ze = λ ()
𝓥-𝟘-bwd .SS.Sup.mor .preserve-+ = λ ()
𝓥-𝟘-bwd .SS.Sup.mor .preserve-· = λ ()
𝓥-𝟘-bwd .SS.Sup.bound .*≈* .prop-setoid._≃m_.func-eq e = S.+-lunit

𝓥-𝟘-iso : Category.Iso SS.Sup.cat (𝓥 OI.𝟘p) (Sup-terminal .HasTerminal.witness)
𝓥-𝟘-iso .Category.Iso.fwd = 𝓥-𝟘-fwd
𝓥-𝟘-iso .Category.Iso.bwd = 𝓥-𝟘-bwd
𝓥-𝟘-iso .Category.Iso.fwd∘bwd≈id =
  MC.≈-trans (MC.≈-sym (SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext _))
             (SemiMod.terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext _)
𝓥-𝟘-iso .Category.Iso.bwd∘fwd≈id .*≈* .prop-setoid._≃m_.func-eq e = λ ()

-- The action of a sum of matrices is the sum of the actions, so the realisation is additive and
-- carries biproducts to biproducts.
app-+ₘ : ∀ {m n} (R T : M.Matrix m n) (v : M.Vec n) (i : Fin m) →
         OS.app (R M.+ₘ T) v i S.≈ (OS.app R v i S.+ OS.app T v i)
app-+ₘ {m} {n} R T v i =
  S.trans (M.Σ-cong {n} (λ j → S.·-+-distribᵣ))
          (S.sym (M.Σ-+ {n} (λ j → R i j S.· v j) (λ j → T i j S.· v j)))

private
  module SCM = CMonEnriched SS.Sup.cmon

𝓥-additive : ∀ {P Q} (f g : P OI.⇒ Q) →
             SC._≈_ (𝓥₁ (OI._+p_ f g)) (SCM._+m_ (𝓥₁ f) (𝓥₁ g))
𝓥-additive {P} {Q} f g .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ _} {v₂ ,ₚ _} e i =
  S.trans (app-+ₘ (f .OI.mat) (g .OI.mat) v₁ i)
          (S.+-cong (M.Σ-cong {P .dim} (λ j → S.·-cong S.refl (e j)))
                    (M.Σ-cong {P .dim} (λ j → S.·-cong S.refl (e j))))

𝓥-zero : ∀ {P Q} → SC._≈_ (𝓥₁ (OI.εp {P} {Q})) (SCM.εm {𝓥 P} {𝓥 Q})
𝓥-zero {P} {Q} .*≈* .prop-setoid._≃m_.func-eq e i =
  S.trans (M.Σ-cong {P .dim} (λ j → S.ε-annihilₗ)) (M.Σ-ε {P .dim})

-- The realised biproduct structure on the realisation of a block order: the laws are the images of
-- the position-order laws under the functor, using additivity.
𝓥-image-biproduct : ∀ P Q → Biproduct SS.Sup.cmon (𝓥 P) (𝓥 Q)
𝓥-image-biproduct P Q .Biproduct.prod = 𝓥 (P OI.⊕ Q)
𝓥-image-biproduct P Q .Biproduct.p₁ = 𝓥₁ (OI.π₁ P Q)
𝓥-image-biproduct P Q .Biproduct.p₂ = 𝓥₁ (OI.π₂ P Q)
𝓥-image-biproduct P Q .Biproduct.in₁ = 𝓥₁ (OI.ι₁ P Q)
𝓥-image-biproduct P Q .Biproduct.in₂ = 𝓥₁ (OI.ι₂ P Q)
𝓥-image-biproduct P Q .Biproduct.id-1 =
  MC.≈-trans (MC.≈-sym (𝓥F .Functor.fmor-comp (OI.π₁ P Q) (OI.ι₁ P Q)))
  (MC.≈-trans (𝓥F .Functor.fmor-cong
                {f₁ = OI._∘_ (OI.π₁ P Q) (OI.ι₁ P Q)} {f₂ = OI.id P}
                (OI.biproduct P Q .Biproduct.id-1))
              (𝓥F .Functor.fmor-id {P}))
𝓥-image-biproduct P Q .Biproduct.id-2 =
  MC.≈-trans (MC.≈-sym (𝓥F .Functor.fmor-comp (OI.π₂ P Q) (OI.ι₂ P Q)))
  (MC.≈-trans (𝓥F .Functor.fmor-cong
                {f₁ = OI._∘_ (OI.π₂ P Q) (OI.ι₂ P Q)} {f₂ = OI.id Q}
                (OI.biproduct P Q .Biproduct.id-2))
              (𝓥F .Functor.fmor-id {Q}))
𝓥-image-biproduct P Q .Biproduct.zero-1 =
  MC.≈-trans (MC.≈-sym (𝓥F .Functor.fmor-comp (OI.π₁ P Q) (OI.ι₂ P Q)))
  (MC.≈-trans (𝓥F .Functor.fmor-cong
                {f₁ = OI._∘_ (OI.π₁ P Q) (OI.ι₂ P Q)} {f₂ = OI.εp {Q} {P}}
                (OI.biproduct P Q .Biproduct.zero-1))
              (𝓥-zero {Q} {P}))
𝓥-image-biproduct P Q .Biproduct.zero-2 =
  MC.≈-trans (MC.≈-sym (𝓥F .Functor.fmor-comp (OI.π₂ P Q) (OI.ι₁ P Q)))
  (MC.≈-trans (𝓥F .Functor.fmor-cong
                {f₁ = OI._∘_ (OI.π₂ P Q) (OI.ι₁ P Q)} {f₂ = OI.εp {P} {Q}}
                (OI.biproduct P Q .Biproduct.zero-2))
              (𝓥-zero {P} {Q}))
𝓥-image-biproduct P Q .Biproduct.id-+ =
  MC.≈-trans (CommutativeMonoid.+-cong (CMonEnriched.homCM SemiMod.cmon-enriched _ _)
               (MC.≈-sym (𝓥F .Functor.fmor-comp (OI.ι₁ P Q) (OI.π₁ P Q)))
               (MC.≈-sym (𝓥F .Functor.fmor-comp (OI.ι₂ P Q) (OI.π₂ P Q))))
  (MC.≈-trans (MC.≈-sym (𝓥-additive (OI._∘_ (OI.ι₁ P Q) (OI.π₁ P Q))
                                    (OI._∘_ (OI.ι₂ P Q) (OI.π₂ P Q))))
  (MC.≈-trans (𝓥F .Functor.fmor-cong
                {f₁ = OI._+p_ (OI._∘_ (OI.ι₁ P Q) (OI.π₁ P Q))
                              (OI._∘_ (OI.ι₂ P Q) (OI.π₂ P Q))}
                {f₂ = OI.id (P OI.⊕ Q)}
                (OI.biproduct P Q .Biproduct.id-+))
              (𝓥F .Functor.fmor-id {P OI.⊕ Q})))

-- The chosen supported biproducts, and the canonical comparison with the realised structure.
Sup-biproduct : ∀ X Y → Biproduct SS.Sup.cmon X Y
Sup-biproduct = SS.Sup.biproduct-s SemiMod.biproduct

𝓥-⊕-iso : ∀ P Q → Category.Iso SS.Sup.cat (𝓥 (P OI.⊕ Q))
                    (Biproduct.prod (Sup-biproduct (𝓥 P) (𝓥 Q)))
𝓥-⊕-iso P Q =
  SC.IsIso→Iso (biproduct-iso SS.Sup.cmon (𝓥-image-biproduct P Q) (Sup-biproduct (𝓥 P) (𝓥 Q)))

-- Fullness: a supported morphism between realisations is determined by its values on the closed
-- basis columns, since every fixed vector is the finite sum of its scaled closed columns and
-- morphisms preserve finite sums.
vec : ∀ (P : Pos) → ∃ₛ (M.Vec (P .dim)) (OS.Fixed P) → M.Vec (P .dim)
vec P (u ,ₚ _) = u

fxd : ∀ (P : Pos) (x : ∃ₛ (M.Vec (P .dim)) (OS.Fixed P)) → OS.Fixed P (vec P x)
fxd P (u ,ₚ p) = p

msum : ∀ (X : Semimodule) {n} → (Fin n → X .Carrier) → X .Carrier
msum X {zero}  f = X .additive .CommutativeMonoid.ε
msum X {suc n} f = X ._+_ (f Fin.zero) (msum X (λ i → f (Fin.suc i)))

mor-msum : ∀ {X Y : Semimodule} (h : X ⇒ Y) {n} (f : Fin n → X .Carrier) →
           Y ._≈_ (h .func (msum X f)) (msum Y (λ i → h .func (f i)))
mor-msum {X} {Y} h {zero}  f = h .preserve-ze
mor-msum {X} {Y} h {suc n} f =
  Y .trans (h .preserve-+) (Y .+-cong (Y .refl) (mor-msum h (λ i → f (Fin.suc i))))

𝓥-msum-vec : ∀ (P : Pos) {n} (f : Fin n → ∃ₛ (M.Vec (P .dim)) (OS.Fixed P)) (q : Fin (P .dim)) →
             vec P (msum (𝓥sm P) f) q S.≈ M.Σ {n} (λ p → vec P (f p) q)
𝓥-msum-vec P {zero}  f q = S.refl
𝓥-msum-vec P {suc n} f q = S.+-cong S.refl (𝓥-msum-vec P (λ i → f (Fin.suc i)) q)

-- A fixed vector is the sum of its scaled closed columns, and so is each closed column against the
-- order, which is what absorption of the recovered matrix needs.
decomp : ∀ (P : Pos) (v : M.Vec (P .dim)) (fx : OS.Fixed P v) (q : Fin (P .dim)) →
         v q S.≈ vec P (msum (𝓥sm P) (λ p → 𝓥sm P ._·_ (v p) (colv P p))) q
decomp P v fx q =
  S.trans (S.sym (fx q))
  (S.trans (M.Σ-cong {P .dim} (λ p → S.·-comm))
           (S.sym (𝓥-msum-vec P (λ p → 𝓥sm P ._·_ (v p) (colv P p)) q)))

decomp-col : ∀ (P : Pos) (p : Fin (P .dim)) (q : Fin (P .dim)) →
             P .ord q p S.≈ vec P (msum (𝓥sm P) (λ j → 𝓥sm P ._·_ (P .ord j p) (colv P j))) q
decomp-col P p q =
  S.trans (S.sym (OI.ord-idem P q p))
  (S.trans (M.Σ-cong {P .dim} (λ j → S.·-comm))
           (S.sym (𝓥-msum-vec P (λ j → 𝓥sm P ._·_ (P .ord j p) (colv P j)) q)))

full-mor : ∀ {P Q} → SS.Sup.Mor (𝓥 P) (𝓥 Q) → P OI.⇒ Q
full-mor {P} {Q} h .OI.mat q p = vec Q (h .SS.Sup.mor .func (colv P p)) q
full-mor {P} {Q} h .OI.absorbed =
  OI.≈ₘ-trans (M.∘-cong left (OI.≈ₘ-refl {M = P .ord})) right
  where
  left : (Q .ord M.∘ (λ q p → vec Q (h .SS.Sup.mor .func (colv P p)) q))
         M.≈ₘ (λ q p → vec Q (h .SS.Sup.mor .func (colv P p)) q)
  left q p = fxd Q (h .SS.Sup.mor .func (colv P p)) q

  right : ((λ q p → vec Q (h .SS.Sup.mor .func (colv P p)) q) M.∘ P .ord)
          M.≈ₘ (λ q p → vec Q (h .SS.Sup.mor .func (colv P p)) q)
  right q p =
    S.sym
      (S.trans (h .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈ (decomp-col P p) q)
      (S.trans (mor-msum (h .SS.Sup.mor) (λ j → 𝓥sm P ._·_ (P .ord j p) (colv P j)) q)
      (S.trans (𝓥-msum-vec Q (λ j → h .SS.Sup.mor .func (𝓥sm P ._·_ (P .ord j p) (colv P j))) q)
      (S.trans (M.Σ-cong {P .dim} (λ j → h .SS.Sup.mor .preserve-· {P .ord j p} {colv P j} q))
               (M.Σ-cong {P .dim} (λ j → S.·-comm))))))

𝓥-full : ∀ {P Q} (h : SS.Sup.Mor (𝓥 P) (𝓥 Q)) → SC._≈_ (𝓥₁ (full-mor h)) h
𝓥-full {P} {Q} h .*≈* .prop-setoid._≃m_.func-eq {v₁ ,ₚ fx₁} {v₂ ,ₚ _} e q =
  S.trans (M.Σ-cong {P .dim} (λ p → S.·-comm))
  (S.trans (M.Σ-cong {P .dim} (λ p → S.sym (h .SS.Sup.mor .preserve-· {v₁ p} {colv P p} q)))
  (S.trans (S.sym (𝓥-msum-vec Q (λ p → h .SS.Sup.mor .func (𝓥sm P ._·_ (v₁ p) (colv P p))) q))
  (S.trans (S.sym (mor-msum (h .SS.Sup.mor) (λ p → 𝓥sm P ._·_ (v₁ p) (colv P p)) q))
           (h .SS.Sup.mor .*→* .prop-setoid._⇒_.func-resp-≈
             (λ q' → S.trans (S.sym (decomp P v₁ fx₁ q')) (e q')) q))))
