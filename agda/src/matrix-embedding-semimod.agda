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
  renaming (S to End𝕀)

-- The embedding factors through the self-dual semimodules: each free object X^ n (an iterated
-- biproduct of 𝕀) carries the self-duality built from those of 𝕀 and 𝟘.
import sd-semimodule
open import Data.Nat using (ℕ; zero; suc)
open import functor using (Functor)

module SDSemiMod = sd-semimodule S

private
  X^-self-dual : ∀ n → Category.Iso SemiMod.cat (X^ n) (SDSemiMod.Dual (X^ n))
  X^-self-dual zero    = SDSemiMod.𝟘≅𝟘*
  X^-self-dual (suc n) = SDSemiMod.⊕-self-dual SDSemiMod.𝕀≅𝕀* (X^-self-dual n)

  X^-pairing-sym : ∀ n {x y} → SDSemiMod.pairing (X^-self-dual n) x y S.≈ SDSemiMod.pairing (X^-self-dual n) y x
  X^-pairing-sym zero    = S.refl
  X^-pairing-sym (suc n) =
    S.trans (SDSemiMod.pairing-⊕ SDSemiMod.𝕀≅𝕀* (X^-self-dual n))
      (S.trans (S.+-cong S.·-comm (X^-pairing-sym n))
        (S.sym (SDSemiMod.pairing-⊕ SDSemiMod.𝕀≅𝕀* (X^-self-dual n))))

fobj-sd : ℕ → SDSemiMod.SelfDual
fobj-sd n .SDSemiMod.SelfDual.obj  = X^ n
fobj-sd n .SDSemiMod.SelfDual.dual = X^-self-dual n
fobj-sd n .SDSemiMod.SelfDual.pairing-sym = X^-pairing-sym n

embed : Functor Mat.cat SDSemiMod.cat
embed .Functor.fobj = fobj-sd
embed .Functor.fmor {m} {n} = F .Functor.fmor {m} {n}
embed .Functor.fmor-cong {m} {n} = F .Functor.fmor-cong {m} {n}
embed .Functor.fmor-id {n} = F .Functor.fmor-id {n}
embed .Functor.fmor-comp {m} {n} {k} = F .Functor.fmor-comp {m} {n} {k}
