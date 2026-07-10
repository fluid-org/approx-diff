{-# OPTIONS --prop --postfix-projections --safe #-}

-- The free commutative semiring on a set X: the provenance polynomials ℕ[X], presented as the
-- term model, with setoid equality the equational theory of commutative semirings. The semiring
-- laws hold by construction, and eval is the homomorphism extending a valuation of the variables.
module semiring-free (X : Set) where

open import Level using (Level; 0ℓ)
open import prop-setoid using (Setoid; IsEquivalence)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)

infixl 20 _+p_
infixl 21 _·p_

data Poly : Set where
  var : X → Poly
  ze un : Poly
  _+p_ _·p_ : Poly → Poly → Poly

data _≈p_ : Poly → Poly → Prop where
  ≈p-refl  : ∀ {p} → p ≈p p
  ≈p-sym   : ∀ {p q} → p ≈p q → q ≈p p
  ≈p-trans : ∀ {p q r} → p ≈p q → q ≈p r → p ≈p r
  +p-cong  : ∀ {p p' q q'} → p ≈p p' → q ≈p q' → (p +p q) ≈p (p' +p q')
  ·p-cong  : ∀ {p p' q q'} → p ≈p p' → q ≈p q' → (p ·p q) ≈p (p' ·p q')
  +p-lunit : ∀ {p} → (ze +p p) ≈p p
  +p-assoc : ∀ {p q r} → ((p +p q) +p r) ≈p (p +p (q +p r))
  +p-comm  : ∀ {p q} → (p +p q) ≈p (q +p p)
  ·p-lunit : ∀ {p} → (un ·p p) ≈p p
  ·p-assoc : ∀ {p q r} → ((p ·p q) ·p r) ≈p (p ·p (q ·p r))
  ·p-comm  : ∀ {p q} → (p ·p q) ≈p (q ·p p)
  distrib  : ∀ {p q r} → (p ·p (q +p r)) ≈p (p ·p q +p p ·p r)
  annihil  : ∀ {p} → (ze ·p p) ≈p ze

setoid : Setoid 0ℓ 0ℓ
setoid .Setoid.Carrier = Poly
setoid .Setoid._≈_ = _≈p_
setoid .Setoid.isEquivalence .IsEquivalence.refl = ≈p-refl
setoid .Setoid.isEquivalence .IsEquivalence.sym = ≈p-sym
setoid .Setoid.isEquivalence .IsEquivalence.trans = ≈p-trans

additive : CommutativeMonoid setoid
additive .CommutativeMonoid.ε = ze
additive .CommutativeMonoid._+_ = _+p_
additive .CommutativeMonoid.+-cong = +p-cong
additive .CommutativeMonoid.+-lunit = +p-lunit
additive .CommutativeMonoid.+-assoc = +p-assoc
additive .CommutativeMonoid.+-comm = +p-comm

multiplicative : CommutativeMonoid setoid
multiplicative .CommutativeMonoid.ε = un
multiplicative .CommutativeMonoid._+_ = _·p_
multiplicative .CommutativeMonoid.+-cong = ·p-cong
multiplicative .CommutativeMonoid.+-lunit = ·p-lunit
multiplicative .CommutativeMonoid.+-assoc = ·p-assoc
multiplicative .CommutativeMonoid.+-comm = ·p-comm

semiring : CommutativeSemiring setoid
semiring .CommutativeSemiring.additive = additive
semiring .CommutativeSemiring.multiplicative = multiplicative
semiring .CommutativeSemiring.·-+-distribₗ = distrib
semiring .CommutativeSemiring.ε-annihilₗ = annihil

-- Freeness: a valuation of the variables in any commutative semiring extends to a homomorphism.
module Eval {o e : Level} {A : Setoid o e} (T : CommutativeSemiring A) (ρ : X → Setoid.Carrier A) where
  private module T = CommutativeSemiring T

  eval : Poly → Setoid.Carrier A
  eval (var x) = ρ x
  eval ze = T.ε
  eval un = T.ι
  eval (p +p q) = eval p T.+ eval q
  eval (p ·p q) = eval p T.· eval q

  eval-resp-≈ : ∀ {p q} → p ≈p q → Setoid._≈_ A (eval p) (eval q)
  eval-resp-≈ ≈p-refl = T.refl
  eval-resp-≈ (≈p-sym e) = T.sym (eval-resp-≈ e)
  eval-resp-≈ (≈p-trans e₁ e₂) = T.trans (eval-resp-≈ e₁) (eval-resp-≈ e₂)
  eval-resp-≈ (+p-cong e₁ e₂) = T.+-cong (eval-resp-≈ e₁) (eval-resp-≈ e₂)
  eval-resp-≈ (·p-cong e₁ e₂) = T.·-cong (eval-resp-≈ e₁) (eval-resp-≈ e₂)
  eval-resp-≈ +p-lunit = T.+-lunit
  eval-resp-≈ +p-assoc = T.+-assoc
  eval-resp-≈ +p-comm = T.+-comm
  eval-resp-≈ ·p-lunit = T.·-lunit
  eval-resp-≈ ·p-assoc = T.·-assoc
  eval-resp-≈ ·p-comm = T.·-comm
  eval-resp-≈ distrib = T.·-+-distribₗ
  eval-resp-≈ annihil = T.ε-annihilₗ

------------------------------------------------------------------------------
-- An (unverified!) normaliser, for testing: polynomials as sorted lists of monomials with coefficients,
-- rendered as strings. Parameterised by an ordering index.
module Normalise (index : X → ℕ) (show-var : X → String) where

  open import Data.Nat using (ℕ; _*_; _<ᵇ_; _+_)
  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.List using (List; []; _∷_; map)
  open import Data.Product using (_,_; _×_)
  open import Data.String using (String) renaming (_++_ to _++s_)
  import Data.Nat.Show

  Monomial : Set
  Monomial = List X

  private
    insert-var : X → Monomial → Monomial
    insert-var x [] = x ∷ []
    insert-var x (y ∷ m) = if index x <ᵇ index y then x ∷ y ∷ m else y ∷ insert-var x m

    mon-* : Monomial → Monomial → Monomial
    mon-* [] m = m
    mon-* (x ∷ m₁) m₂ = insert-var x (mon-* m₁ m₂)

    mon-<ᵇ : Monomial → Monomial → Bool
    mon-<ᵇ [] [] = false
    mon-<ᵇ [] (_ ∷ _) = true
    mon-<ᵇ (_ ∷ _) [] = false
    mon-<ᵇ (x ∷ m₁) (y ∷ m₂) =
      if index x <ᵇ index y then true else (if index y <ᵇ index x then false else mon-<ᵇ m₁ m₂)

    mon-=ᵇ : Monomial → Monomial → Bool
    mon-=ᵇ [] [] = true
    mon-=ᵇ [] (_ ∷ _) = false
    mon-=ᵇ (_ ∷ _) [] = false
    mon-=ᵇ (x ∷ m₁) (y ∷ m₂) =
      if index x <ᵇ index y then false else (if index y <ᵇ index x then false else mon-=ᵇ m₁ m₂)

  NormalForm : Set
  NormalForm = List (Monomial × ℕ)

  private
    add-term : Monomial × ℕ → NormalForm → NormalForm
    add-term (m , c) [] = (m , c) ∷ []
    add-term (m , c) ((m' , c') ∷ p) =
      if mon-=ᵇ m m' then (m , c + c') ∷ p
      else (if mon-<ᵇ m m' then (m , c) ∷ (m' , c') ∷ p else (m' , c') ∷ add-term (m , c) p)

    nf-add : NormalForm → NormalForm → NormalForm
    nf-add [] p = p
    nf-add (t ∷ p₁) p₂ = add-term t (nf-add p₁ p₂)

    nf-mul : NormalForm → NormalForm → NormalForm
    nf-mul [] _ = []
    nf-mul ((m , c) ∷ p₁) p₂ = nf-add (map (λ (m' , c') → mon-* m m' , c * c') p₂) (nf-mul p₁ p₂)

  norm : Poly → NormalForm
  norm (var x) = ((x ∷ []) , 1) ∷ []
  norm ze = []
  norm un = ([] , 1) ∷ []
  norm (p +p q) = nf-add (norm p) (norm q)
  norm (p ·p q) = nf-mul (norm p) (norm q)

  private
    show-mon : Monomial → String
    show-mon [] = "1"
    show-mon (x ∷ []) = show-var x
    show-mon (x ∷ m) = show-var x ++s "·" ++s show-mon m

    show-term : Monomial × ℕ → String
    show-term (m , 1) = show-mon m
    show-term (m , c) = Data.Nat.Show.show c ++s "·" ++s show-mon m

  pretty : Poly → String
  pretty p = go (norm p)
    where
      go : NormalForm → String
      go [] = "0"
      go (t ∷ []) = show-term t
      go (t ∷ p) = show-term t ++s " + " ++s go p
