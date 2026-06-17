{-# OPTIONS --postfix-projections --prop --safe #-}

module mat where

open import Level using (0ℓ; _⊔_)
open import prop using (⊤; tt; _∧_; _,_; proj₁; proj₂)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)

-- Free f.g. S-semimodules ("matrices"), with vectors as inductive Data.Vec
-- (instead of functions Fin n → Carrier).
module Mat {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

  open CommutativeSemiring S public
  open import Data.Nat using (ℕ; zero; suc)
  import Data.Vec as V
  open V public using ([]; _∷_)

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

  +ᵥ-runit : ∀ {n} {v : Vec n} → (v +ᵥ εᵥ) ≈ᵥ v
  +ᵥ-runit {v = []}    = tt
  +ᵥ-runit {v = x ∷ v} = trans +-comm +-lunit , +ᵥ-runit

  scale-cong : ∀ {n} {a a'} {u v : Vec n} → a ≈ a' → u ≈ᵥ v → scale a u ≈ᵥ scale a' v
  scale-cong {u = []}    {[]}    _  _       = tt
  scale-cong {u = _ ∷ _} {_ ∷ _} a≈ (p , q) = ·-cong a≈ p , scale-cong a≈ q

  scale-+ₗ : ∀ {n} {a b} {v : Vec n} → scale (a + b) v ≈ᵥ (scale a v +ᵥ scale b v)
  scale-+ₗ {v = []}    = tt
  scale-+ₗ {v = _ ∷ _} = ·-+-distribᵣ , scale-+ₗ

  scale-· : ∀ {n} {a b} {v : Vec n} → scale (a · b) v ≈ᵥ scale a (scale b v)
  scale-· {v = []}    = tt
  scale-· {v = _ ∷ _} = ·-assoc , scale-·

  scale-ι : ∀ {n} {v : Vec n} → scale ι v ≈ᵥ v
  scale-ι {v = []}    = tt
  scale-ι {v = _ ∷ _} = ·-lunit , scale-ι

  scale-0ₗ : ∀ {n} {v : Vec n} → scale ε v ≈ᵥ εᵥ
  scale-0ₗ {v = []}    = tt
  scale-0ₗ {v = _ ∷ _} = ε-annihilₗ , scale-0ₗ

  open import Data.Nat using () renaming (_+_ to _+ℕ_)
  open V using (_++_)

  ++-cong : ∀ {m n} {u u' : Vec m} {v v' : Vec n} → u ≈ᵥ u' → v ≈ᵥ v' → (u ++ v) ≈ᵥ (u' ++ v')
  ++-cong {u = []}    {[]}    _        q = q
  ++-cong {u = _ ∷ _} {_ ∷ _} (p , ps) q = p , ++-cong ps q

  ++-+ᵥ : ∀ {m n} {u u' : Vec m} {v v' : Vec n} →
          ((u +ᵥ u') ++ (v +ᵥ v')) ≈ᵥ ((u ++ v) +ᵥ (u' ++ v'))
  ++-+ᵥ {u = []}    {[]}                              = ≈ᵥ-refl
  ++-+ᵥ {u = _ ∷ _} {_ ∷ _} {v = v} {v' = v'}        = refl , ++-+ᵥ {v = v} {v' = v'}

  ++-scale : ∀ {m n} {a} {u : Vec m} {v : Vec n} → scale a (u ++ v) ≈ᵥ (scale a u ++ scale a v)
  ++-scale {u = []}                  = ≈ᵥ-refl
  ++-scale {u = _ ∷ _} {v = v}       = refl , ++-scale {v = v}

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

  open import cmon-enriched using (Biproduct; biproducts→products)
  open import categories using (HasProducts)

  vtake : ∀ m {n} → Vec (m +ℕ n) → Vec m
  vtake zero    _        = []
  vtake (suc m) (x ∷ xs) = x ∷ vtake m xs

  vdrop : ∀ m {n} → Vec (m +ℕ n) → Vec n
  vdrop zero    xs       = xs
  vdrop (suc m) (x ∷ xs) = vdrop m xs

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

------------------------------------------------------------------------------
-- Embedding of free S-semimodules into all S-semimodules, with terminal/product preservation and
-- self-duality of the free objects.

module Embedding {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Nat using () renaming (_+_ to _+ℕ_)
  open import Data.Vec using (_++_; _∷_; [])
  open import Data.Product using (_,_)
  open import prop-setoid using () renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
  open import commutative-monoid using (CommutativeMonoid)
  open import cmon-enriched using (biproducts→products)
  open import functor using (Functor)
  import semimodule
  import finite-product-functor

  private
    module FD = Mat S
    module SM = semimodule S
  open SM
  open SM._⇒_
  open SM._≈m_
  open Category SM.cat using (IsIso; Iso; Iso-trans; Iso-sym; IsIso→Iso)

  ----------------------------------------------------------------------------
  -- Object part: Sⁿ as a semimodule, with Vec n's (Data.Vec) structure.

  fobj : ℕ → Semimodule
  fobj n .Semimodule.setoid .Setoid.Carrier = FD.Vec n
  fobj n .Semimodule.setoid .Setoid._≈_ = FD._≈ᵥ_
  fobj n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.refl = FD.≈ᵥ-refl
  fobj n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.sym = FD.≈ᵥ-sym
  fobj n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.trans = FD.≈ᵥ-trans
  fobj n .Semimodule.additive .CommutativeMonoid.ε = FD.εᵥ
  fobj n .Semimodule.additive .CommutativeMonoid._+_ = FD._+ᵥ_
  fobj n .Semimodule.additive .CommutativeMonoid.+-cong = FD.+ᵥ-cong
  fobj n .Semimodule.additive .CommutativeMonoid.+-lunit = FD.+ᵥ-lunit
  fobj n .Semimodule.additive .CommutativeMonoid.+-assoc = FD.+ᵥ-assoc
  fobj n .Semimodule.additive .CommutativeMonoid.+-comm = FD.+ᵥ-comm
  fobj n .Semimodule._·_ = FD.scale
  fobj n .Semimodule.·-cong = FD.scale-cong
  fobj n .Semimodule.·-mul = FD.scale-·
  fobj n .Semimodule.·-unit = FD.scale-ι
  fobj n .Semimodule.+-distribʳ = FD.scale-+ₗ
  fobj n .Semimodule.+-distribˡ = FD.scale-+ᵥ
  fobj n .Semimodule.zero-distribʳ = FD.scale-0ₗ
  fobj n .Semimodule.zero-distribˡ = FD.scale-εᵥ

  F : Functor FD.cat SM.cat
  F .Functor.fobj = fobj
  F .Functor.fmor f .*→* ._⇒s_.func = f .FD.func
  F .Functor.fmor f .*→* ._⇒s_.func-resp-≈ = f .FD.func-resp-≈
  F .Functor.fmor f .preserve-ze = f .FD.ε-preserving
  F .Functor.fmor f .preserve-+ = f .FD.+-preserving
  F .Functor.fmor f .preserve-· = f .FD.scale-preserving
  F .Functor.fmor-cong {f₂ = f₂} f₁≈f₂ .*≈* ._≈s_.func-eq u≈v =
    FD.≈ᵥ-trans (f₁≈f₂ _) (f₂ .FD.func-resp-≈ u≈v)
  F .Functor.fmor-id .*≈* ._≈s_.func-eq u≈v = u≈v
  F .Functor.fmor-comp f g .*≈* ._≈s_.func-eq u≈v =
    f .FD.func-resp-≈ (g .FD.func-resp-≈ u≈v)

  module FPF = finite-product-functor F

  ----------------------------------------------------------------------------
  -- Terminal preservation: fobj 0 (the one-point Vec 0) is isomorphic to 𝟘.

  term-inv : 𝟘 ⇒ fobj 0
  term-inv .*→* ._⇒s_.func _ = FD.εᵥ
  term-inv .*→* ._⇒s_.func-resp-≈ _ = FD.≈ᵥ-refl
  term-inv .preserve-ze = FD.≈ᵥ-refl
  term-inv .preserve-+ = FD.≈ᵥ-refl
  term-inv .preserve-· = FD.≈ᵥ-refl

  F-preserve-terminal : FPF.preserve-chosen-terminal FD.terminal SM.terminal
  F-preserve-terminal .IsIso.inverse = term-inv
  F-preserve-terminal .IsIso.f∘inverse≈id .*≈* ._≈s_.func-eq _ = tt
  F-preserve-terminal .IsIso.inverse∘f≈id .*≈* ._≈s_.func-eq {_} {v} _ = FD.[]-≈ᵥ v

  ----------------------------------------------------------------------------
  -- Product preservation: fobj (m + n) ≅ fobj m ⊕ fobj n, the inverse being _++_.

  combine : ∀ {m n} → (fobj m ⊕ fobj n) ⇒ fobj (m +ℕ n)
  combine .*→* ._⇒s_.func (u , w) = u ++ w
  combine .*→* ._⇒s_.func-resp-≈ (u≈ , w≈) = FD.++-cong u≈ w≈
  combine {m} {n} .preserve-ze = FD.++-εᵥ {m} {n}
  combine {m} {n} .preserve-+ {u , w} {u' , w'} = FD.++-+ᵥ {u = u} {u'} {w} {w'}
  combine {m} {n} .preserve-· {a} {u , w} = FD.≈ᵥ-sym (FD.++-scale {u = u} {w})

  -- combine ∘ fwd ≈ id, by recursion on the split point.  The biproduct-derived
  -- pairing adds εᵥ on each side, hence the +ᵥ εᵥ / εᵥ +ᵥ terms.
  combine-fwd : ∀ m {n} {v : FD.Vec (m +ℕ n)} →
                ((FD.vtake m v FD.+ᵥ FD.εᵥ) ++ (FD.εᵥ FD.+ᵥ FD.vdrop m v)) FD.≈ᵥ v
  combine-fwd zero                    = FD.+ᵥ-lunit
  combine-fwd (suc m) {n} {v = x ∷ v} = FD.trans FD.+-comm FD.+-lunit , combine-fwd m {n}

  F-preserve-products : FPF.preserve-chosen-products FD.products
                          (biproducts→products SM.cmon-enriched SM.biproduct)
  F-preserve-products {m} {n} .IsIso.inverse = combine {m} {n}
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id .*≈* ._≈s_.func-eq {u₁ , w₁} {u₂ , w₂} (u≈ , w≈) =
    FD.≈ᵥ-trans (FD.+ᵥ-cong (FD.vtake-++ {m} {n} {u₁} {w₁}) FD.≈ᵥ-refl) (FD.≈ᵥ-trans FD.+ᵥ-runit u≈) ,
    FD.≈ᵥ-trans (FD.+ᵥ-cong FD.≈ᵥ-refl (FD.vdrop-++ {m} {n} {u₁} {w₁})) (FD.≈ᵥ-trans FD.+ᵥ-lunit w≈)
  F-preserve-products {m} {n} .IsIso.inverse∘f≈id .*≈* ._≈s_.func-eq {v} v≈ =
    FD.≈ᵥ-trans (combine-fwd m {n} {v}) v≈

  ----------------------------------------------------------------------------
  -- Self-duality of the free S-semimodules.

  1≅𝕀 : Iso (fobj 1) 𝕀
  1≅𝕀 .Iso.fwd .*→* ._⇒s_.func (x ∷ []) = x
  1≅𝕀 .Iso.fwd .*→* ._⇒s_.func-resp-≈ {x ∷ []} {y ∷ []} (p , _) = p
  1≅𝕀 .Iso.fwd .preserve-ze = FD.refl
  1≅𝕀 .Iso.fwd .preserve-+ {x ∷ []} {y ∷ []} = FD.refl
  1≅𝕀 .Iso.fwd .preserve-· {a} {x ∷ []} = FD.refl
  1≅𝕀 .Iso.bwd .*→* ._⇒s_.func x = x ∷ []
  1≅𝕀 .Iso.bwd .*→* ._⇒s_.func-resp-≈ x≈y = x≈y , tt
  1≅𝕀 .Iso.bwd .preserve-ze = FD.refl , tt
  1≅𝕀 .Iso.bwd .preserve-+ = FD.refl , tt
  1≅𝕀 .Iso.bwd .preserve-· = FD.refl , tt
  1≅𝕀 .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq x≈x' = x≈x'
  1≅𝕀 .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq {x ∷ []} {y ∷ []} h = h

  fobj-self-dual : ∀ n → Iso (fobj n) (Dual (fobj n))
  fobj-self-dual zero =
    Iso-trans (IsIso→Iso F-preserve-terminal)
              (Iso-trans (Iso-sym Dual-𝟘) (Dual-iso (IsIso→Iso F-preserve-terminal)))
  fobj-self-dual (suc n) =
    Iso-trans (IsIso→Iso (F-preserve-products {1} {n}))
              (Iso-trans (⊕-iso (Iso-trans 1≅𝕀 (Iso-trans 𝕀≅𝕀* (Dual-iso 1≅𝕀))) (fobj-self-dual n))
                         (Iso-trans (Iso-sym Dual-⊕-iso) (Dual-iso (IsIso→Iso (F-preserve-products {1} {n})))))

  ----------------------------------------------------------------------------
  -- Conjugate of a free-object morphism: the generic conjugate instantiated at
  -- the free-object self-dualities.  conj-pairing then gives the conjugate
  -- relation ⟨ conj-free f y , x ⟩ ≈ ⟨ y , f x ⟩.

  conj-free : ∀ {m n} → (fobj m ⇒ fobj n) → (fobj n ⇒ fobj m)
  conj-free {m} {n} = conj (fobj-self-dual m) (fobj-self-dual n)
