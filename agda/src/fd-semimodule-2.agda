{-# OPTIONS --postfix-projections --prop --safe #-}

module fd-semimodule-2 where

open import Level using (_⊔_)
open import prop using (⊤; tt; _∧_; _,_; proj₁; proj₂)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)

-- FDSemiMod with vectors as inductive Data.Vec, instead of functions Fin n → Carrier.
module FDSemiMod₂ {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

  open CommutativeSemiring S public
  open import Data.Nat using (ℕ; zero; suc)
  import Data.Vec as V
  open V using ([]; _∷_)

  ----------------------------------------------------------------------------
  -- The carrier: vectors S^n as inductive data.

  Vec : ℕ → Set o
  Vec n = V.Vec Carrier n

  -- Pointwise equality.
  infix 4 _≈ᵥ_
  _≈ᵥ_ : ∀ {n} → Vec n → Vec n → Prop ℓ
  []      ≈ᵥ []      = ⊤
  (x ∷ u) ≈ᵥ (y ∷ v) = (x ≈ y) ∧ (u ≈ᵥ v)

  ≈ᵥ-refl : ∀ {n} {v : Vec n} → v ≈ᵥ v
  ≈ᵥ-refl {v = []}    = tt
  ≈ᵥ-refl {v = x ∷ v} = refl , ≈ᵥ-refl

  ≈ᵥ-sym : ∀ {n} {u v : Vec n} → u ≈ᵥ v → v ≈ᵥ u
  ≈ᵥ-sym {u = []} {[]} _              = tt
  ≈ᵥ-sym {u = _ ∷ _} {_ ∷ _} (p , q)  = sym p , ≈ᵥ-sym q

  ≈ᵥ-trans : ∀ {n} {u v w : Vec n} → u ≈ᵥ v → v ≈ᵥ w → u ≈ᵥ w
  ≈ᵥ-trans {u = []} {[]} {[]} _ _                         = tt
  ≈ᵥ-trans {u = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , q) (p' , q')  = trans p p' , ≈ᵥ-trans q q'

  -- Zero vector.
  εᵥ : ∀ {n} → Vec n
  εᵥ {zero}  = []
  εᵥ {suc n} = ε ∷ εᵥ

  -- Pointwise addition and scalar multiplication.
  infixl 20 _+ᵥ_
  _+ᵥ_ : ∀ {n} → Vec n → Vec n → Vec n
  _+ᵥ_ = V.zipWith _+_

  scale : ∀ {n} → Carrier → Vec n → Vec n
  scale a = V.map (a ·_)

  ----------------------------------------------------------------------------
  -- Morphisms: linear maps S^n → S^m.

  record _⇒_ (n m : ℕ) : Set (o ⊔ ℓ) where
    no-eta-equality
    field
      func             : Vec n → Vec m
      func-resp-≈      : ∀ {u v} → u ≈ᵥ v → func u ≈ᵥ func v
      +-preserving     : ∀ {u v} → func (u +ᵥ v) ≈ᵥ (func u +ᵥ func v)
      ε-preserving     : func εᵥ ≈ᵥ εᵥ
      scale-preserving : ∀ {a v} → func (scale a v) ≈ᵥ scale a (func v)
  open _⇒_ public

  infix 4 _≃_
  _≃_ : ∀ {n m} → n ⇒ m → n ⇒ m → Prop (o ⊔ ℓ)
  f ≃ g = ∀ v → f .func v ≈ᵥ g .func v

  ≃-isEquiv : ∀ {n m} → IsEquivalence (_≃_ {n} {m})
  ≃-isEquiv .IsEquivalence.refl v = ≈ᵥ-refl
  ≃-isEquiv .IsEquivalence.sym f≃g v = ≈ᵥ-sym (f≃g v)
  ≃-isEquiv .IsEquivalence.trans f≃g g≃h v = ≈ᵥ-trans (f≃g v) (g≃h v)

  ----------------------------------------------------------------------------
  -- Category of free semimodules.

  id : ∀ {n} → n ⇒ n
  id .func v = v
  id .func-resp-≈ u≈ᵥ = u≈ᵥ
  id .+-preserving = ≈ᵥ-refl
  id .ε-preserving = ≈ᵥ-refl
  id .scale-preserving = ≈ᵥ-refl

  infixl 21 _∘_
  _∘_ : ∀ {n m k} → m ⇒ k → n ⇒ m → n ⇒ k
  (g ∘ f) .func v = g .func (f .func v)
  (g ∘ f) .func-resp-≈ u≈ᵥ = g .func-resp-≈ (f .func-resp-≈ u≈ᵥ)
  (g ∘ f) .+-preserving = ≈ᵥ-trans (g .func-resp-≈ (f .+-preserving)) (g .+-preserving)
  (g ∘ f) .ε-preserving = ≈ᵥ-trans (g .func-resp-≈ (f .ε-preserving)) (g .ε-preserving)
  (g ∘ f) .scale-preserving = ≈ᵥ-trans (g .func-resp-≈ (f .scale-preserving)) (g .scale-preserving)

  cat : Category _ _ _
  cat .Category.obj = ℕ
  cat .Category._⇒_ n m = n ⇒ m
  cat .Category._≈_ = _≃_
  cat .Category.isEquiv = ≃-isEquiv
  cat .Category.id n = id
  cat .Category._∘_ = _∘_
  cat .Category.∘-cong {f₁ = F₁} {g₂ = G₂} F≃ G≃ v = ≈ᵥ-trans (F₁ .func-resp-≈ (G≃ v)) (F≃ (G₂ .func v))
  cat .Category.id-left _ = ≈ᵥ-refl
  cat .Category.id-right _ = ≈ᵥ-refl
  cat .Category.assoc _ _ _ _ = ≈ᵥ-refl

  ----------------------------------------------------------------------------
  -- Vector algebra.

  []-≈ᵥ : ∀ (w : Vec 0) → εᵥ ≈ᵥ w
  []-≈ᵥ [] = tt

  +ᵥ-cong : ∀ {n} {u u' v v' : Vec n} → u ≈ᵥ u' → v ≈ᵥ v' → (u +ᵥ v) ≈ᵥ (u' +ᵥ v')
  +ᵥ-cong {u = []} {[]} {[]} {[]} _ _ = tt
  +ᵥ-cong {u = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} (p , q) (p' , q') = +-cong p p' , +ᵥ-cong q q'

  +ᵥ-lunit : ∀ {n} {v : Vec n} → (εᵥ +ᵥ v) ≈ᵥ v
  +ᵥ-lunit {v = []} = tt
  +ᵥ-lunit {v = x ∷ v} = +-lunit , +ᵥ-lunit

  +ᵥ-assoc : ∀ {n} {u v w : Vec n} → ((u +ᵥ v) +ᵥ w) ≈ᵥ (u +ᵥ (v +ᵥ w))
  +ᵥ-assoc {u = []} {[]} {[]} = tt
  +ᵥ-assoc {u = _ ∷ _} {_ ∷ _} {_ ∷ _} = +-assoc , +ᵥ-assoc

  +ᵥ-comm : ∀ {n} {u v : Vec n} → (u +ᵥ v) ≈ᵥ (v +ᵥ u)
  +ᵥ-comm {u = []} {[]} = tt
  +ᵥ-comm {u = _ ∷ _} {_ ∷ _} = +-comm , +ᵥ-comm

  +ᵥ-interchange : ∀ {n} {a b c d : Vec n} → ((a +ᵥ b) +ᵥ (c +ᵥ d)) ≈ᵥ ((a +ᵥ c) +ᵥ (b +ᵥ d))
  +ᵥ-interchange {a = []} {[]} {[]} {[]} = tt
  +ᵥ-interchange {a = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} = +-interchange , +ᵥ-interchange

  scale-εᵥ : ∀ {n} {a} → scale a (εᵥ {n}) ≈ᵥ εᵥ
  scale-εᵥ {zero}  = tt
  scale-εᵥ {suc n} = ε-annihilᵣ , scale-εᵥ

  scale-+ᵥ : ∀ {n} {a} {u v : Vec n} → scale a (u +ᵥ v) ≈ᵥ (scale a u +ᵥ scale a v)
  scale-+ᵥ {u = []} {[]} = tt
  scale-+ᵥ {u = _ ∷ _} {_ ∷ _} = ·-+-distribₗ , scale-+ᵥ

  ----------------------------------------------------------------------------
  -- 0 is a zero object.

  open import categories using (HasTerminal; IsTerminal; HasInitial; IsInitial)
  open HasTerminal ; open IsTerminal ; open HasInitial ; open IsInitial

  terminal : HasTerminal cat
  terminal .witness = 0
  terminal .is-terminal .to-terminal .func _ = []
  terminal .is-terminal .to-terminal .func-resp-≈ _ = tt
  terminal .is-terminal .to-terminal .+-preserving = tt
  terminal .is-terminal .to-terminal .ε-preserving = tt
  terminal .is-terminal .to-terminal .scale-preserving = tt
  terminal .is-terminal .to-terminal-ext f v = []-≈ᵥ (f .func v)

  initial : HasInitial cat
  initial .witness = 0
  initial .is-initial .from-initial .func _ = εᵥ
  initial .is-initial .from-initial .func-resp-≈ _ = ≈ᵥ-refl
  initial .is-initial .from-initial .+-preserving = ≈ᵥ-sym +ᵥ-lunit
  initial .is-initial .from-initial .ε-preserving = ≈ᵥ-refl
  initial .is-initial .from-initial .scale-preserving = ≈ᵥ-sym scale-εᵥ
  initial .is-initial .from-initial-ext f [] = ≈ᵥ-sym (f .ε-preserving)

  ----------------------------------------------------------------------------
  -- CMon-enrichment.

  open import cmon-enriched using (CMonEnriched)
  open import commutative-monoid using (CommutativeMonoid)
  open CMonEnriched

  εₘ : ∀ {n m} → n ⇒ m
  εₘ .func _ = εᵥ
  εₘ .func-resp-≈ _ = ≈ᵥ-refl
  εₘ .+-preserving = ≈ᵥ-sym +ᵥ-lunit
  εₘ .ε-preserving = ≈ᵥ-refl
  εₘ .scale-preserving = ≈ᵥ-sym scale-εᵥ

  infixl 21 _+ₘ_
  _+ₘ_ : ∀ {n m} → n ⇒ m → n ⇒ m → n ⇒ m
  (f +ₘ g) .func v = f .func v +ᵥ g .func v
  (f +ₘ g) .func-resp-≈ p = +ᵥ-cong (f .func-resp-≈ p) (g .func-resp-≈ p)
  (f +ₘ g) .+-preserving = ≈ᵥ-trans (+ᵥ-cong (f .+-preserving) (g .+-preserving)) +ᵥ-interchange
  (f +ₘ g) .ε-preserving = ≈ᵥ-trans (+ᵥ-cong (f .ε-preserving) (g .ε-preserving)) +ᵥ-lunit
  (f +ₘ g) .scale-preserving = ≈ᵥ-trans (+ᵥ-cong (f .scale-preserving) (g .scale-preserving)) (≈ᵥ-sym scale-+ᵥ)

  cmon : CMonEnriched cat
  cmon .homCM n m .CommutativeMonoid.ε = εₘ
  cmon .homCM n m .CommutativeMonoid._+_ = _+ₘ_
  cmon .homCM n m .CommutativeMonoid.+-cong p q v = +ᵥ-cong (p v) (q v)
  cmon .homCM n m .CommutativeMonoid.+-lunit v = +ᵥ-lunit
  cmon .homCM n m .CommutativeMonoid.+-assoc v = +ᵥ-assoc
  cmon .homCM n m .CommutativeMonoid.+-comm v = +ᵥ-comm
  cmon .comp-bilinear₁ f₁ f₂ g v = ≈ᵥ-refl
  cmon .comp-bilinear₂ f g₁ g₂ v = f .+-preserving
  cmon .comp-bilinear-ε₁ f v = ≈ᵥ-refl
  cmon .comp-bilinear-ε₂ f v = f .ε-preserving

  ----------------------------------------------------------------------------
  -- Biproducts: direct sum m + n, via recursive vtake/vdrop and _++_.

  open import Data.Nat using () renaming (_+_ to _+ℕ_)
  open V using (_++_)
  open import cmon-enriched using (Biproduct; biproducts→products)
  open import categories using (HasProducts)

  vtake : ∀ m {n} → Vec (m +ℕ n) → Vec m
  vtake zero    _        = []
  vtake (suc m) (x ∷ xs) = x ∷ vtake m xs

  vdrop : ∀ m {n} → Vec (m +ℕ n) → Vec n
  vdrop zero    xs       = xs
  vdrop (suc m) (x ∷ xs) = vdrop m xs

  +ᵥ-runit : ∀ {n} {v : Vec n} → (v +ᵥ εᵥ) ≈ᵥ v
  +ᵥ-runit {v = []}    = tt
  +ᵥ-runit {v = x ∷ v} = trans +-comm +-lunit , +ᵥ-runit

  vtake-cong : ∀ m {n} {u v : Vec (m +ℕ n)} → u ≈ᵥ v → vtake m u ≈ᵥ vtake m v
  vtake-cong zero _ = tt
  vtake-cong (suc m) {u = _ ∷ _} {_ ∷ _} (p , q) = p , vtake-cong m q

  vdrop-cong : ∀ m {n} {u v : Vec (m +ℕ n)} → u ≈ᵥ v → vdrop m u ≈ᵥ vdrop m v
  vdrop-cong zero p = p
  vdrop-cong (suc m) {u = _ ∷ _} {_ ∷ _} (_ , q) = vdrop-cong m q

  vtake-εᵥ : ∀ m {n} → vtake m (εᵥ {m +ℕ n}) ≈ᵥ εᵥ
  vtake-εᵥ zero    = tt
  vtake-εᵥ (suc m) = refl , vtake-εᵥ m

  vdrop-εᵥ : ∀ m {n} → vdrop m (εᵥ {m +ℕ n}) ≈ᵥ εᵥ {n}
  vdrop-εᵥ zero    = ≈ᵥ-refl
  vdrop-εᵥ (suc m) = vdrop-εᵥ m

  vtake-+ᵥ : ∀ m {n} {u v : Vec (m +ℕ n)} → vtake m (u +ᵥ v) ≈ᵥ (vtake m u +ᵥ vtake m v)
  vtake-+ᵥ zero = tt
  vtake-+ᵥ (suc m) {u = _ ∷ _} {_ ∷ _} = refl , vtake-+ᵥ m

  vdrop-+ᵥ : ∀ m {n} {u v : Vec (m +ℕ n)} → vdrop m (u +ᵥ v) ≈ᵥ (vdrop m u +ᵥ vdrop m v)
  vdrop-+ᵥ zero = ≈ᵥ-refl
  vdrop-+ᵥ (suc m) {u = _ ∷ _} {_ ∷ _} = vdrop-+ᵥ m

  vtake-scale : ∀ m {n} {a} {v : Vec (m +ℕ n)} → vtake m (scale a v) ≈ᵥ scale a (vtake m v)
  vtake-scale zero = tt
  vtake-scale (suc m) {v = _ ∷ _} = refl , vtake-scale m

  vdrop-scale : ∀ m {n} {a} {v : Vec (m +ℕ n)} → vdrop m (scale a v) ≈ᵥ scale a (vdrop m v)
  vdrop-scale zero = ≈ᵥ-refl
  vdrop-scale (suc m) {v = _ ∷ _} = vdrop-scale m

  ++-εᵥ : ∀ {m n} → (εᵥ {m} ++ εᵥ {n}) ≈ᵥ εᵥ {m +ℕ n}
  ++-εᵥ {zero}      = ≈ᵥ-refl
  ++-εᵥ {suc m} {n} = refl , ++-εᵥ {m} {n}

  vtake-++ : ∀ {m n} {u : Vec m} {v : Vec n} → vtake m (u ++ v) ≈ᵥ u
  vtake-++ {u = []}    = tt
  vtake-++ {u = _ ∷ _} = refl , vtake-++

  vdrop-++ : ∀ {m n} {u : Vec m} {v : Vec n} → vdrop m (u ++ v) ≈ᵥ v
  vdrop-++ {u = []} = ≈ᵥ-refl
  vdrop-++ {m = suc m} {n = n} {u = _ ∷ _} = vdrop-++ {m = m} {n = n}

  in₁-cong : ∀ {m n} {u v : Vec m} → u ≈ᵥ v → (u ++ εᵥ {n}) ≈ᵥ (v ++ εᵥ)
  in₁-cong {u = []} {[]}_ = ≈ᵥ-refl
  in₁-cong {u = _ ∷ _} {_ ∷ _} (p , q) = p , in₁-cong q

  in₁-+ : ∀ {m n} {u v : Vec m} → ((u +ᵥ v) ++ εᵥ {n}) ≈ᵥ ((u ++ εᵥ) +ᵥ (v ++ εᵥ))
  in₁-+ {u = []} {[]} = ≈ᵥ-sym +ᵥ-lunit
  in₁-+ {n = n} {u = _ ∷ _} {_ ∷ _} = refl , in₁-+ {n = n}

  in₁-scale : ∀ {m n} {a} {v : Vec m} → ((scale a v) ++ εᵥ {n}) ≈ᵥ scale a (v ++ εᵥ)
  in₁-scale {v = []}            = ≈ᵥ-sym scale-εᵥ
  in₁-scale {n = n} {v = _ ∷ _} = refl , in₁-scale {n = n}

  in₂-cong : ∀ {m n} {u v : Vec n} → u ≈ᵥ v → (εᵥ {m} ++ u) ≈ᵥ (εᵥ ++ v)
  in₂-cong {m = zero}  p = p
  in₂-cong {m = suc m} p = refl , in₂-cong p

  in₂-+ : ∀ {m n} {u v : Vec n} → (εᵥ {m} ++ (u +ᵥ v)) ≈ᵥ ((εᵥ ++ u) +ᵥ (εᵥ ++ v))
  in₂-+ {m = zero}            = ≈ᵥ-refl
  in₂-+ {m = suc m} {n = n}   = sym +-lunit , in₂-+ {n = n}

  in₂-scale : ∀ {m n} {a} {v : Vec n} → (εᵥ {m} ++ scale a v) ≈ᵥ scale a (εᵥ {m} ++ v)
  in₂-scale {m = zero}            = ≈ᵥ-refl
  in₂-scale {m = suc m} {n = n}   = sym ε-annihilᵣ , in₂-scale {n = n}

  id-+-lem : ∀ m {n} {v : Vec (m +ℕ n)} → (((vtake m v) ++ εᵥ {n}) +ᵥ (εᵥ {m} ++ (vdrop m v))) ≈ᵥ v
  id-+-lem zero                = +ᵥ-lunit
  id-+-lem (suc m) {v = x ∷ v} = trans +-comm +-lunit , id-+-lem m

  -- Projections / injections.
  p₁ : ∀ {m n} → (m +ℕ n) ⇒ m
  p₁ {m} .func = vtake m
  p₁ {m} .func-resp-≈ = vtake-cong m
  p₁ {m} .+-preserving = vtake-+ᵥ m
  p₁ {m} .ε-preserving = vtake-εᵥ m
  p₁ {m} .scale-preserving = vtake-scale m

  p₂ : ∀ {m n} → (m +ℕ n) ⇒ n
  p₂ {m} .func = vdrop m
  p₂ {m} .func-resp-≈ = vdrop-cong m
  p₂ {m} .+-preserving = vdrop-+ᵥ m
  p₂ {m} .ε-preserving = vdrop-εᵥ m
  p₂ {m} .scale-preserving = vdrop-scale m

  in₁ : ∀ {m n} → m ⇒ (m +ℕ n)
  in₁ {m} {n} .func v = v ++ εᵥ {n}
  in₁ {m} {n} .func-resp-≈ = in₁-cong {m} {n}
  in₁ {m} {n} .+-preserving = in₁-+ {m} {n}
  in₁ {m} {n} .ε-preserving = ++-εᵥ {m} {n}
  in₁ {m} {n} .scale-preserving = in₁-scale {m} {n}

  in₂ : ∀ {m n} → n ⇒ (m +ℕ n)
  in₂ {m} {n} .func v = εᵥ {m} ++ v
  in₂ {m} {n} .func-resp-≈ = in₂-cong {m} {n}
  in₂ {m} {n} .+-preserving = in₂-+ {m} {n}
  in₂ {m} {n} .ε-preserving = ++-εᵥ {m} {n}
  in₂ {m} {n} .scale-preserving = in₂-scale {m} {n}

  biproduct : ∀ m n → Biproduct cmon m n
  biproduct m n .Biproduct.prod = m +ℕ n
  biproduct m n .Biproduct.p₁ = p₁ {m} {n}
  biproduct m n .Biproduct.p₂ = p₂ {m} {n}
  biproduct m n .Biproduct.in₁ = in₁ {m} {n}
  biproduct m n .Biproduct.in₂ = in₂ {m} {n}
  biproduct m n .Biproduct.id-1 v = vtake-++ {m} {n}
  biproduct m n .Biproduct.id-2 v = vdrop-++ {m} {n}
  biproduct m n .Biproduct.zero-1 v = vtake-++ {m} {n}
  biproduct m n .Biproduct.zero-2 v = vdrop-++ {m} {n}
  biproduct m n .Biproduct.id-+ v = id-+-lem m

  products : HasProducts cat
  products = biproducts→products cmon biproduct
