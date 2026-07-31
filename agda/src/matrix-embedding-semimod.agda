{-# OPTIONS --postfix-projections --prop --safe #-}

-- matrix-embedding instantiated at 𝒞 = SemiMod(S), X = 𝕀.  The 𝕀-endomorphisms
-- are the scalars (composition = multiplication, commutative since S is), so this
-- yields the full-and-faithful embedding 𝓖 : Mat(S) ↪ SemiMod(S).

open import Level using (0ℓ)
open import prop using (tt)
open import prop-setoid using (Setoid) renaming (_≃m_ to _≈s_)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; IsInitial; IsTerminal; HasTerminal)
import semimodule
import matrix-embedding

module matrix-embedding-semimod {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

private
  module SemiMod = semimodule S
  module S = CommutativeSemiring S

open SemiMod using (𝟘; 𝕀; ε-map; terminal; _⇒_; _∘_; _≈m_)
open SemiMod._⇒_
open SemiMod._≈m_
open SemiMod.Semimodule using (sym; trans)

-- 𝟘 is the zero object: initial as well as terminal.
𝟘-initial : IsInitial SemiMod.cat 𝟘
𝟘-initial .IsInitial.from-initial {M} = ε-map 𝟘 M
𝟘-initial .IsInitial.from-initial-ext {M} f .*≈* ._≈s_.func-eq _ =
  M .sym (M .trans (f .func-resp-≈ tt) (f .preserve-ze))

𝟘-terminal : IsTerminal SemiMod.cat 𝟘
𝟘-terminal = terminal .HasTerminal.is-terminal

-- End(𝕀) ≅ S: a 𝕀-endomorphism is multiplication by a scalar (h x = x · h ι),
-- so composition of endomorphisms commutes.
private
  ·-runit : ∀ {y} → (y S.· S.ι) S.≈ y
  ·-runit = S.trans S.·-comm S.·-lunit

  scalar-endo : (h : 𝕀 ⇒ 𝕀) (y : S.Carrier) → h .func y S.≈ (y S.· h .func S.ι)
  scalar-endo h y = S.trans (h .func-resp-≈ (S.sym ·-runit)) (h .preserve-·)

  endo-comm : (f g : 𝕀 ⇒ 𝕀) (x : S.Carrier) → f .func (g .func x) S.≈ g .func (f .func x)
  endo-comm f g x =
    S.trans (scalar-endo f (g .func x))
    (S.trans (S.·-cong (scalar-endo g x) S.refl)
    (S.trans S.·-assoc
    (S.trans (S.·-cong S.refl S.·-comm)
    (S.trans (S.sym S.·-assoc)
    (S.trans (S.·-cong (S.sym (scalar-endo f x)) S.refl)
              (S.sym (scalar-endo g (f .func x))))))))

∘-comm : ∀ {f g : 𝕀 ⇒ 𝕀} → (f ∘ g) ≈m (g ∘ f)
∘-comm {f} {g} .*≈* ._≈s_.func-eq {x₁} x₁≈x₂ =
  S.trans (endo-comm f g x₁) (g .func-resp-≈ (f .func-resp-≈ x₁≈x₂))

open import matrix-embedding SemiMod.cmon-enriched SemiMod.biproduct 𝟘 𝟘-initial 𝟘-terminal 𝕀 (λ {f} {g} → ∘-comm {f} {g}) public

-- The embedding factors through the self-dual semimodules: each free object X^ n is isomorphic to the free
-- self-dual semimodule S^ n. The two differ only by the unit law at width one, where S^ 1 is 𝕀 and X^ 1 is
-- 𝕀 ⊕ 𝟘.
import sd-semimodule
open import Data.Nat using (ℕ; zero; suc)
open import functor using (Functor)

module SDSemiMod = sd-semimodule S
open SDSemiMod using (S^_)
open import prop-setoid using (module ≈-Reasoning)
open import commutative-semiring using (_⇒h_)

private
  module C = Category SemiMod.cat
  open C.Iso

-- The free object of width n, as a self-dual semimodule.
X^≅S^ : ∀ n → C.Iso (X^ n) (SDSemiMod.SelfDual.obj (S^ n))
X^≅S^ zero = C.Iso-refl
X^≅S^ (suc zero) = SemiMod.⊕-runit-iso
X^≅S^ (suc (suc n)) = SDSemiMod.⊕-iso C.Iso-refl (X^≅S^ (suc n))

embed : Functor Mat.cat SDSemiMod.cat
embed .Functor.fobj n = S^ n
embed .Functor.fmor {m} {n} M = X^≅S^ n .fwd C.∘ (F .Functor.fmor M C.∘ X^≅S^ m .bwd)
embed .Functor.fmor-cong {m} {n} e =
  C.∘-cong (C.≈-refl {f = X^≅S^ n .fwd}) (C.∘-cong (F .Functor.fmor-cong e) (C.≈-refl {f = X^≅S^ m .bwd}))
embed .Functor.fmor-id {n} = begin
    X^≅S^ n .fwd C.∘ (F .Functor.fmor (Mat.cat .Category.id n) C.∘ X^≅S^ n .bwd)
  ≈⟨ C.∘-cong (C.≈-refl {f = X^≅S^ n .fwd}) (C.∘-cong (F .Functor.fmor-id {n}) (C.≈-refl {f = X^≅S^ n .bwd})) ⟩
    X^≅S^ n .fwd C.∘ (C.id _ C.∘ X^≅S^ n .bwd)
  ≈⟨ C.∘-cong (C.≈-refl {f = X^≅S^ n .fwd}) (C.id-left {f = X^≅S^ n .bwd}) ⟩
    X^≅S^ n .fwd C.∘ X^≅S^ n .bwd
  ≈⟨ X^≅S^ n .fwd∘bwd≈id ⟩
    C.id _
  ∎
  where open ≈-Reasoning C.isEquiv
embed .Functor.fmor-comp {x} {y} {z} f g = begin
    X^≅S^ z .fwd C.∘ (F .Functor.fmor (Mat.cat .Category._∘_ f g) C.∘ X^≅S^ x .bwd)
  ≈⟨ C.∘-cong (C.≈-refl {f = X^≅S^ z .fwd}) (C.∘-cong (F .Functor.fmor-comp f g) (C.≈-refl {f = X^≅S^ x .bwd})) ⟩
    X^≅S^ z .fwd C.∘ ((F .Functor.fmor f C.∘ F .Functor.fmor g) C.∘ X^≅S^ x .bwd)
  ≈˘⟨ C.∘-cong (C.≈-refl {f = X^≅S^ z .fwd}) (C.∘-cong (C.∘-cong (C.≈-refl {f = F .Functor.fmor f}) (C.id-left {f = F .Functor.fmor g})) (C.≈-refl {f = X^≅S^ x .bwd})) ⟩
    X^≅S^ z .fwd C.∘ ((F .Functor.fmor f C.∘ (C.id _ C.∘ F .Functor.fmor g)) C.∘ X^≅S^ x .bwd)
  ≈˘⟨ C.∘-cong (C.≈-refl {f = X^≅S^ z .fwd}) (C.∘-cong (C.∘-cong (C.≈-refl {f = F .Functor.fmor f}) (C.∘-cong (X^≅S^ y .bwd∘fwd≈id) (C.≈-refl {f = F .Functor.fmor g}))) (C.≈-refl {f = X^≅S^ x .bwd})) ⟩
    X^≅S^ z .fwd C.∘ ((F .Functor.fmor f C.∘ ((X^≅S^ y .bwd C.∘ X^≅S^ y .fwd) C.∘ F .Functor.fmor g)) C.∘ X^≅S^ x .bwd)
  ≈⟨ C.∘-cong (C.≈-refl {f = X^≅S^ z .fwd}) (C.∘-cong (C.∘-cong (C.≈-refl {f = F .Functor.fmor f}) (C.assoc (X^≅S^ y .bwd) (X^≅S^ y .fwd) (F .Functor.fmor g))) (C.≈-refl {f = X^≅S^ x .bwd})) ⟩
    X^≅S^ z .fwd C.∘ ((F .Functor.fmor f C.∘ (X^≅S^ y .bwd C.∘ (X^≅S^ y .fwd C.∘ F .Functor.fmor g))) C.∘ X^≅S^ x .bwd)
  ≈˘⟨ C.∘-cong (C.≈-refl {f = X^≅S^ z .fwd}) (C.∘-cong (C.assoc (F .Functor.fmor f) (X^≅S^ y .bwd) (X^≅S^ y .fwd C.∘ F .Functor.fmor g)) (C.≈-refl {f = X^≅S^ x .bwd})) ⟩
    X^≅S^ z .fwd C.∘ (((F .Functor.fmor f C.∘ X^≅S^ y .bwd) C.∘ (X^≅S^ y .fwd C.∘ F .Functor.fmor g)) C.∘ X^≅S^ x .bwd)
  ≈⟨ C.∘-cong (C.≈-refl {f = X^≅S^ z .fwd}) (C.assoc (F .Functor.fmor f C.∘ X^≅S^ y .bwd) (X^≅S^ y .fwd C.∘ F .Functor.fmor g) (X^≅S^ x .bwd)) ⟩
    X^≅S^ z .fwd C.∘ ((F .Functor.fmor f C.∘ X^≅S^ y .bwd) C.∘ ((X^≅S^ y .fwd C.∘ F .Functor.fmor g) C.∘ X^≅S^ x .bwd))
  ≈˘⟨ C.assoc (X^≅S^ z .fwd) (F .Functor.fmor f C.∘ X^≅S^ y .bwd) ((X^≅S^ y .fwd C.∘ F .Functor.fmor g) C.∘ X^≅S^ x .bwd) ⟩
    (X^≅S^ z .fwd C.∘ (F .Functor.fmor f C.∘ X^≅S^ y .bwd)) C.∘ ((X^≅S^ y .fwd C.∘ F .Functor.fmor g) C.∘ X^≅S^ x .bwd)
  ≈⟨ C.∘-cong (C.≈-refl {f = X^≅S^ z .fwd C.∘ (F .Functor.fmor f C.∘ X^≅S^ y .bwd)}) (C.assoc (X^≅S^ y .fwd) (F .Functor.fmor g) (X^≅S^ x .bwd)) ⟩
    (X^≅S^ z .fwd C.∘ (F .Functor.fmor f C.∘ X^≅S^ y .bwd)) C.∘ (X^≅S^ y .fwd C.∘ (F .Functor.fmor g C.∘ X^≅S^ x .bwd))
  ∎
  where open ≈-Reasoning C.isEquiv

------------------------------------------------------------------------------
-- The scalars are the 𝕀-endomorphisms, in both directions: a scalar acts by multiplication, and an
-- endomorphism is recovered as its value at ι. Packaging both as semiring homomorphisms lets the
-- generic embedding be read at S rather than at EndX.

mult-endo : S.Carrier → SemiMod._⇒_ 𝕀 𝕀
mult-endo s .SemiMod._⇒_.*→* .prop-setoid._⇒_.func y = y S.· s
mult-endo s .SemiMod._⇒_.*→* .prop-setoid._⇒_.func-resp-≈ e = S.·-cong e S.refl
mult-endo s .SemiMod._⇒_.preserve-ze = S.ε-annihilₗ
mult-endo s .SemiMod._⇒_.preserve-+ = S.·-+-distribᵣ
mult-endo s .SemiMod._⇒_.preserve-· = S.·-assoc

into : S ⇒h EndX
into ._⇒h_.f = mult-endo
into ._⇒h_.f-cong e .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' = S.·-cong y≈y' e
into ._⇒h_.f-+ .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' =
  S.trans (S.·-cong y≈y' S.refl) S.·-+-distribₗ
into ._⇒h_.f-· .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' =
  S.trans (S.·-cong y≈y' S.refl)
    (S.trans (S.·-cong S.refl S.·-comm) (S.sym (S.·-assoc)))
into ._⇒h_.f-ε .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' =
  S.trans (S.·-cong y≈y' S.refl) S.ε-annihilᵣ
into ._⇒h_.f-ι .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq y≈y' =
  S.trans (S.·-cong y≈y' S.refl) (S.trans S.·-comm S.·-lunit)

endo-scalar : SemiMod._⇒_ 𝕀 𝕀 → S.Carrier
endo-scalar h = h .SemiMod._⇒_.*→* .prop-setoid._⇒_.func S.ι

outof : EndX ⇒h S
outof ._⇒h_.f = endo-scalar
outof ._⇒h_.f-cong e = e .SemiMod._≈m_.*≈* .prop-setoid._≃m_.func-eq S.refl
outof ._⇒h_.f-+ = S.refl
outof ._⇒h_.f-· {a} {b} =
  S.trans (scalar-endo a (endo-scalar b)) S.·-comm
outof ._⇒h_.f-ε = S.refl
outof ._⇒h_.f-ι = S.refl

open AtSemiring S into outof public
  using (mat→mor; mor→mat; mat→mor-εₘ; mat→mor-+ₘ; mat→mor-faithful; mat→mor-full; module MatS)

-- The scalar embedding is injective: evaluating at ι recovers the scalar.
into-inj : ∀ {a b} → (mult-endo a) ≈m (mult-endo b) → a S.≈ b
into-inj h = S.trans (S.sym S.·-lunit) (S.trans (h .*≈* ._≈s_.func-eq S.refl) S.·-lunit)

-- And it retracts: an endomorphism is multiplication by its value at ι.
into-outof : ∀ (φ : 𝕀 ⇒ 𝕀) → (mult-endo (endo-scalar φ)) ≈m φ
into-outof φ .*≈* ._≈s_.func-eq {y₁} {y₂} y₁≈y₂ =
  S.trans (S.sym (scalar-endo φ y₁)) (φ .func-resp-≈ y₁≈y₂)
