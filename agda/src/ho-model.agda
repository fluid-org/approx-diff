{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

open import Level using (0ℓ)
open import prop using (_,_; proj₁; proj₂; tt)
open import categories using (Category; HasTerminal; HasProducts)
import join-semilattice-category as JoinSemiLat

------------------------------------------------------------------------------
-- MatRep model: the full subcategory of JoinSemiLat on iterated biproducts of TWO,
-- equivalent to Mat(Two) (≃ FinRel) via matrix-embedding.
module MatRep where
  open import categories using (HasInitial; IsInitial; IsTerminal)
  open import cmon-enriched using (cmon+products→biproducts; biproducts→products)
  open import commutative-monoid using (CommutativeMonoid; _=[_]>_)
  open import commutative-semiring using (CommutativeSemiring)
  open import prop-setoid using (Setoid; module ≈-Reasoning)
  open import setoid-cat using (SetoidCat)
  open import two using (Two; O; I; semiring; Two-setoid)
  import cmon-enriched as CMon
  import join-semilattice as J
  import preorder
  import two
  open J._≃m_ using (eqfunc)
  open preorder._≃m_ using (eqfun)
  open JoinSemiLat._≃m_
  open JoinSemiLat._⇒_

  open Category JoinSemiLat.cat
  open CMon.CMonEnriched JoinSemiLat.cmon-enriched
    using (_+m_; εm; +m-runit; comp-bilinear-ε₁; comp-bilinear-ε₂; comp-bilinear₁; comp-bilinear₂)

  TWO : JoinSemiLat.Obj
  TWO = JoinSemiLat.TWO

  private
    module homCM {x y} = CommutativeMonoid (CMon.CMonEnriched.homCM JoinSemiLat.cmon-enriched x y)

  -- Semiring isomorphism Two ↔ End(TWO) in JoinSemiLat. Each End(TWO) preserves ⊥, so is determined by its
  -- value at I (either εm or id).
  module scalar where
    to : Two → TWO ⇒ TWO
    to O = εm
    to I = id TWO

    from : TWO ⇒ TWO → Two
    from f = fun f I

    to-cong : ∀ {a b} → a two.≃ b → to a ≈ to b
    to-cong {O} {O} _ = ≈-refl
    to-cong {O} {I} (_ , ())
    to-cong {I} {O} (() , _)
    to-cong {I} {I} _ = ≈-refl

    preserves-ε : to O ≈ εm
    preserves-ε = ≈-refl

    preserves-ι : to I ≈ id TWO
    preserves-ι = ≈-refl

    preserves-+ : ∀ {a b} → to (a two.⊔ b) ≈ to a +m to b
    preserves-+ {O} {O} = ≈-sym homCM.+-lunit
    preserves-+ {O} {I} = ≈-sym homCM.+-lunit
    preserves-+ {I} {O} = ≈-sym +m-runit
    preserves-+ {I} {I} = I-idem
      where
        I-idem : id TWO ≈ id TWO +m id TWO
        I-idem .f≃f .eqfunc .eqfun O = two.≤-refl {O} , two.≤-refl {O}
        I-idem .f≃f .eqfunc .eqfun I = two.≤-refl {I} , two.≤-refl {I}

    preserves-· : ∀ {a b} → to (a two.⊓ b) ≈ to a ∘ to b
    preserves-· {O} {O} = ≈-sym (comp-bilinear-ε₁ εm)
    preserves-· {O} {I} = ≈-sym (comp-bilinear-ε₁ (id TWO))
    preserves-· {I} {O} = ≈-sym id-left
    preserves-· {I} {I} = ≈-sym id-left

    from-cong : ∀ {f g : TWO ⇒ TWO} → f ≈ g → from f two.≃ from g
    from-cong p = p .f≃f .eqfunc .eqfun I

    from∘to : ∀ a → from (to a) two.≃ a
    from∘to O = two.≃-refl {O}
    from∘to I = two.≃-refl {I}

    -- End(TWO) is determined by f(I).
    to∘from : ∀ (f : TWO ⇒ TWO) → to (from f) ≈ f
    to∘from f .f≃f .eqfunc .eqfun O with fun f I
    ... | O = tt , ⊥-preserving-≃ f .proj₁
    ... | I = tt , ⊥-preserving-≃ f .proj₁
    to∘from f .f≃f .eqfunc .eqfun I with fun f I
    ... | O = two.≃-refl {O}
    ... | I = two.≃-refl {I}

    open import prop-setoid using () renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
    open _⇒s_
    open _≈s_

    iso : Category.Iso (SetoidCat 0ℓ 0ℓ) two.Two-setoid (Category.hom-setoid JoinSemiLat.cat TWO TWO)
    iso .Category.Iso.fwd .func = to
    iso .Category.Iso.fwd .func-resp-≈ = to-cong
    iso .Category.Iso.bwd .func = from
    iso .Category.Iso.bwd .func-resp-≈ = from-cong
    iso .Category.Iso.fwd∘bwd≈id .func-eq {f₁} {f₂} f₁≈f₂ = ≈-trans (to∘from f₁) f₁≈f₂
    iso .Category.Iso.bwd∘fwd≈id .func-eq {a₁} {a₂} a₁≈a₂ = two.≃-trans (from∘to a₁) a₁≈a₂

    open CommutativeSemiring two.semiring using (additive)
    open CMon.CMonEnriched

    cmon-hom : additive =[ iso .Category.Iso.fwd ]> homCM JoinSemiLat.cmon-enriched TWO TWO
    cmon-hom ._=[_]>_.preserve-ε = preserves-ε
    cmon-hom ._=[_]>_.preserve-+ {a} {b} = preserves-+ {a} {b}

  private
    import matrix-embedding
    module MatRep = matrix-embedding
      JoinSemiLat.cmon-enriched
      (cmon+products→biproducts JoinSemiLat.cmon-enriched JoinSemiLat.products)
      (HasTerminal.witness JoinSemiLat.terminal)
      (HasInitial.is-initial JoinSemiLat.initial)
      (HasTerminal.is-terminal JoinSemiLat.terminal)
      TWO
      two.Two-setoid
      two.semiring
      scalar.iso
      scalar.cmon-hom
      scalar.preserves-ι
      (λ {a} {b} → scalar.preserves-· {a} {b})
  open MatRep public
