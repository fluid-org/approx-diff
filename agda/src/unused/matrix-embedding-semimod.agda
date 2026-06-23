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
  module SM = semimodule S
  module S = CommutativeSemiring S

open SM using (𝟘; 𝕀; ε-map)
open SM._⇒_
open SM._≈m_
open SM.Semimodule using (sym; trans)

-- 𝟘 is the zero object: initial as well as terminal.
𝟘-initial : IsInitial SM.cat 𝟘
𝟘-initial .IsInitial.from-initial {M} = ε-map 𝟘 M
𝟘-initial .IsInitial.from-initial-ext {M} f .*≈* ._≈s_.func-eq _ =
  M .sym (M .trans (f .func-resp-≈ tt) (f .preserve-ze))

𝟘-terminal : IsTerminal SM.cat 𝟘
𝟘-terminal = SM.terminal .HasTerminal.is-terminal

-- End(𝕀) ≅ S: a 𝕀-endomorphism is multiplication by a scalar (h x = x · h ι),
-- so composition of endomorphisms commutes.
private
  ·-runit : ∀ {y} → (y S.· S.ι) S.≈ y
  ·-runit = S.trans S.·-comm S.·-lunit

  scalar-endo : (h : 𝕀 SM.⇒ 𝕀) (y : S.Carrier) → h .func y S.≈ (y S.· h .func S.ι)
  scalar-endo h y = S.trans (h .func-resp-≈ (S.sym ·-runit)) (h .preserve-·)

  endo-comm : (f g : 𝕀 SM.⇒ 𝕀) (x : S.Carrier) → f .func (g .func x) S.≈ g .func (f .func x)
  endo-comm f g x =
    S.trans (scalar-endo f (g .func x))
    (S.trans (S.·-cong (scalar-endo g x) S.refl)
    (S.trans S.·-assoc
    (S.trans (S.·-cong S.refl S.·-comm)
    (S.trans (S.sym S.·-assoc)
    (S.trans (S.·-cong (S.sym (scalar-endo f x)) S.refl)
              (S.sym (scalar-endo g (f .func x))))))))

∘-comm : ∀ {f g : 𝕀 SM.⇒ 𝕀} → (f SM.∘ g) SM.≈m (g SM.∘ f)
∘-comm {f} {g} .*≈* ._≈s_.func-eq {x₁} x₁≈x₂ =
  S.trans (endo-comm f g x₁) (g .func-resp-≈ (f .func-resp-≈ x₁≈x₂))

open import matrix-embedding SM.cmon-enriched SM.biproduct 𝟘 𝟘-initial 𝟘-terminal 𝕀 (λ {f} {g} → ∘-comm {f} {g}) public
