{-# OPTIONS --postfix-projections --prop --safe #-}

module mat where

open import Level using (0ℓ; _⊔_)
open import prop using (tt; _,_; proj₁; proj₂; _⇔_; sym-⇔; trans-⇔)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)

-- Free f.g. S-semimodules ("matrices"), with vectors as inductive Data.Vec
-- (instead of functions Fin n → Carrier).
module Mat {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

  module S = CommutativeSemiring S
  open import prop using (⊤; _∧_)
  open import Data.Nat using (ℕ; zero; suc)
  import Data.Vec as V
  open V public using ([]; _∷_)

  ----------------------------------------------------------------------------
  -- The carrier: vectors S^n as inductive data.

  Vec : ℕ → Set o
  Vec n = V.Vec S.Carrier n

  -- Pointwise equality.
  infix 4 _≈ᵥ_
  _≈ᵥ_ : ∀ {n} → Vec n → Vec n → Prop ℓ
  []      ≈ᵥ []      = ⊤
  (x ∷ u) ≈ᵥ (y ∷ v) = (x S.≈ y) ∧ (u ≈ᵥ v)

  ≈ᵥ-refl : ∀ {n} {v : Vec n} → v ≈ᵥ v
  ≈ᵥ-refl {v = []}    = tt
  ≈ᵥ-refl {v = x ∷ v} = S.refl , ≈ᵥ-refl

  ≈ᵥ-sym : ∀ {n} {u v : Vec n} → u ≈ᵥ v → v ≈ᵥ u
  ≈ᵥ-sym {u = []} {[]} _              = tt
  ≈ᵥ-sym {u = _ ∷ _} {_ ∷ _} (p , q)  = S.sym p , ≈ᵥ-sym q

  ≈ᵥ-trans : ∀ {n} {u v w : Vec n} → u ≈ᵥ v → v ≈ᵥ w → u ≈ᵥ w
  ≈ᵥ-trans {u = []} {[]} {[]} _ _                         = tt
  ≈ᵥ-trans {u = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , q) (p' , q')  = S.trans p p' , ≈ᵥ-trans q q'

  -- Zero vector.
  εᵥ : ∀ {n} → Vec n
  εᵥ {zero}  = []
  εᵥ {suc n} = S.ε ∷ εᵥ

  -- Pointwise addition and scalar multiplication.
  infixl 20 _+ᵥ_
  _+ᵥ_ : ∀ {n} → Vec n → Vec n → Vec n
  _+ᵥ_ = V.zipWith S._+_

  scale : ∀ {n} → S.Carrier → Vec n → Vec n
  scale a = V.map (a S.·_)

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
  +ᵥ-cong {u = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} (p , q) (p' , q') = S.+-cong p p' , +ᵥ-cong q q'

  +ᵥ-lunit : ∀ {n} {v : Vec n} → (εᵥ +ᵥ v) ≈ᵥ v
  +ᵥ-lunit {v = []} = tt
  +ᵥ-lunit {v = x ∷ v} = S.+-lunit , +ᵥ-lunit

  +ᵥ-assoc : ∀ {n} {u v w : Vec n} → ((u +ᵥ v) +ᵥ w) ≈ᵥ (u +ᵥ (v +ᵥ w))
  +ᵥ-assoc {u = []} {[]} {[]} = tt
  +ᵥ-assoc {u = _ ∷ _} {_ ∷ _} {_ ∷ _} = S.+-assoc , +ᵥ-assoc

  +ᵥ-comm : ∀ {n} {u v : Vec n} → (u +ᵥ v) ≈ᵥ (v +ᵥ u)
  +ᵥ-comm {u = []} {[]} = tt
  +ᵥ-comm {u = _ ∷ _} {_ ∷ _} = S.+-comm , +ᵥ-comm

  +ᵥ-interchange : ∀ {n} {a b c d : Vec n} → ((a +ᵥ b) +ᵥ (c +ᵥ d)) ≈ᵥ ((a +ᵥ c) +ᵥ (b +ᵥ d))
  +ᵥ-interchange {a = []} {[]} {[]} {[]} = tt
  +ᵥ-interchange {a = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} = S.+-interchange , +ᵥ-interchange

  scale-εᵥ : ∀ {n} {a} → scale a (εᵥ {n}) ≈ᵥ εᵥ
  scale-εᵥ {zero}  = tt
  scale-εᵥ {suc n} = S.ε-annihilᵣ , scale-εᵥ

  scale-+ᵥ : ∀ {n} {a} {u v : Vec n} → scale a (u +ᵥ v) ≈ᵥ (scale a u +ᵥ scale a v)
  scale-+ᵥ {u = []} {[]} = tt
  scale-+ᵥ {u = _ ∷ _} {_ ∷ _} = S.·-+-distribₗ , scale-+ᵥ

  +ᵥ-runit : ∀ {n} {v : Vec n} → (v +ᵥ εᵥ) ≈ᵥ v
  +ᵥ-runit {v = []}    = tt
  +ᵥ-runit {v = x ∷ v} = S.trans S.+-comm S.+-lunit , +ᵥ-runit

  scale-cong : ∀ {n} {a a'} {u v : Vec n} → a S.≈ a' → u ≈ᵥ v → scale a u ≈ᵥ scale a' v
  scale-cong {u = []}    {[]}    _  _       = tt
  scale-cong {u = _ ∷ _} {_ ∷ _} a≈ (p , q) = S.·-cong a≈ p , scale-cong a≈ q

  scale-+ₗ : ∀ {n} {a b} {v : Vec n} → scale (a S.+ b) v ≈ᵥ (scale a v +ᵥ scale b v)
  scale-+ₗ {v = []}    = tt
  scale-+ₗ {v = _ ∷ _} = S.·-+-distribᵣ , scale-+ₗ

  scale-· : ∀ {n} {a b} {v : Vec n} → scale (a S.· b) v ≈ᵥ scale a (scale b v)
  scale-· {v = []}    = tt
  scale-· {v = _ ∷ _} = S.·-assoc , scale-·

  scale-ι : ∀ {n} {v : Vec n} → scale S.ι v ≈ᵥ v
  scale-ι {v = []}    = tt
  scale-ι {v = _ ∷ _} = S.·-lunit , scale-ι

  scale-0ₗ : ∀ {n} {v : Vec n} → scale S.ε v ≈ᵥ εᵥ
  scale-0ₗ {v = []}    = tt
  scale-0ₗ {v = _ ∷ _} = S.ε-annihilₗ , scale-0ₗ

  open import Data.Nat using () renaming (_+_ to _+ℕ_)
  open V using (_++_)

  ++-cong : ∀ {m n} {u u' : Vec m} {v v' : Vec n} → u ≈ᵥ u' → v ≈ᵥ v' → (u ++ v) ≈ᵥ (u' ++ v')
  ++-cong {u = []}    {[]}    _        q = q
  ++-cong {u = _ ∷ _} {_ ∷ _} (p , ps) q = p , ++-cong ps q

  ++-+ᵥ : ∀ {m n} {u u' : Vec m} {v v' : Vec n} →
          ((u +ᵥ u') ++ (v +ᵥ v')) ≈ᵥ ((u ++ v) +ᵥ (u' ++ v'))
  ++-+ᵥ {u = []}    {[]}                              = ≈ᵥ-refl
  ++-+ᵥ {u = _ ∷ _} {_ ∷ _} {v = v} {v' = v'}        = S.refl , ++-+ᵥ {v = v} {v' = v'}

  ++-scale : ∀ {m n} {a} {u : Vec m} {v : Vec n} → scale a (u ++ v) ≈ᵥ (scale a u ++ scale a v)
  ++-scale {u = []}                  = ≈ᵥ-refl
  ++-scale {u = _ ∷ _} {v = v}       = S.refl , ++-scale {v = v}

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
  vtake-εᵥ (suc m) = S.refl , vtake-εᵥ m

  vdrop-εᵥ : ∀ m {n} → vdrop m (εᵥ {m +ℕ n}) ≈ᵥ εᵥ {n}
  vdrop-εᵥ zero    = ≈ᵥ-refl
  vdrop-εᵥ (suc m) = vdrop-εᵥ m

  vtake-+ᵥ : ∀ m {n} {u v : Vec (m +ℕ n)} → vtake m (u +ᵥ v) ≈ᵥ (vtake m u +ᵥ vtake m v)
  vtake-+ᵥ zero = tt
  vtake-+ᵥ (suc m) {u = _ ∷ _} {_ ∷ _} = S.refl , vtake-+ᵥ m

  vdrop-+ᵥ : ∀ m {n} {u v : Vec (m +ℕ n)} → vdrop m (u +ᵥ v) ≈ᵥ (vdrop m u +ᵥ vdrop m v)
  vdrop-+ᵥ zero = ≈ᵥ-refl
  vdrop-+ᵥ (suc m) {u = _ ∷ _} {_ ∷ _} = vdrop-+ᵥ m

  vtake-scale : ∀ m {n} {a} {v : Vec (m +ℕ n)} → vtake m (scale a v) ≈ᵥ scale a (vtake m v)
  vtake-scale zero = tt
  vtake-scale (suc m) {v = _ ∷ _} = S.refl , vtake-scale m

  vdrop-scale : ∀ m {n} {a} {v : Vec (m +ℕ n)} → vdrop m (scale a v) ≈ᵥ scale a (vdrop m v)
  vdrop-scale zero = ≈ᵥ-refl
  vdrop-scale (suc m) {v = _ ∷ _} = vdrop-scale m

  ++-εᵥ : ∀ {m n} → (εᵥ {m} ++ εᵥ {n}) ≈ᵥ εᵥ {m +ℕ n}
  ++-εᵥ {zero}      = ≈ᵥ-refl
  ++-εᵥ {suc m} {n} = S.refl , ++-εᵥ {m} {n}

  vtake-++ : ∀ {m n} {u : Vec m} {v : Vec n} → vtake m (u ++ v) ≈ᵥ u
  vtake-++ {u = []}    = tt
  vtake-++ {u = _ ∷ _} = S.refl , vtake-++

  vdrop-++ : ∀ {m n} {u : Vec m} {v : Vec n} → vdrop m (u ++ v) ≈ᵥ v
  vdrop-++ {u = []} = ≈ᵥ-refl
  vdrop-++ {m = suc m} {n = n} {u = _ ∷ _} = vdrop-++ {m = m} {n = n}

  in₁-cong : ∀ {m n} {u v : Vec m} → u ≈ᵥ v → (u ++ εᵥ {n}) ≈ᵥ (v ++ εᵥ)
  in₁-cong {u = []} {[]}_ = ≈ᵥ-refl
  in₁-cong {u = _ ∷ _} {_ ∷ _} (p , q) = p , in₁-cong q

  in₁-+ : ∀ {m n} {u v : Vec m} → ((u +ᵥ v) ++ εᵥ {n}) ≈ᵥ ((u ++ εᵥ) +ᵥ (v ++ εᵥ))
  in₁-+ {u = []} {[]} = ≈ᵥ-sym +ᵥ-lunit
  in₁-+ {n = n} {u = _ ∷ _} {_ ∷ _} = S.refl , in₁-+ {n = n}

  in₁-scale : ∀ {m n} {a} {v : Vec m} → ((scale a v) ++ εᵥ {n}) ≈ᵥ scale a (v ++ εᵥ)
  in₁-scale {v = []}            = ≈ᵥ-sym scale-εᵥ
  in₁-scale {n = n} {v = _ ∷ _} = S.refl , in₁-scale {n = n}

  in₂-cong : ∀ {m n} {u v : Vec n} → u ≈ᵥ v → (εᵥ {m} ++ u) ≈ᵥ (εᵥ ++ v)
  in₂-cong {m = zero}  p = p
  in₂-cong {m = suc m} p = S.refl , in₂-cong p

  in₂-+ : ∀ {m n} {u v : Vec n} → (εᵥ {m} ++ (u +ᵥ v)) ≈ᵥ ((εᵥ ++ u) +ᵥ (εᵥ ++ v))
  in₂-+ {m = zero}            = ≈ᵥ-refl
  in₂-+ {m = suc m} {n = n}   = S.sym S.+-lunit , in₂-+ {n = n}

  in₂-scale : ∀ {m n} {a} {v : Vec n} → (εᵥ {m} ++ scale a v) ≈ᵥ scale a (εᵥ {m} ++ v)
  in₂-scale {m = zero}            = ≈ᵥ-refl
  in₂-scale {m = suc m} {n = n}   = S.sym S.ε-annihilᵣ , in₂-scale {n = n}

  id-+-lem : ∀ m {n} {v : Vec (m +ℕ n)} → (((vtake m v) ++ εᵥ {n}) +ᵥ (εᵥ {m} ++ (vdrop m v))) ≈ᵥ v
  id-+-lem zero                = +ᵥ-lunit
  id-+-lem (suc m) {v = x ∷ v} = S.trans S.+-comm S.+-lunit , id-+-lem m

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
-- Embedding of free S-semimodules into all S-semimodules, with terminal/product preservation.

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
  open Category SM.cat using (IsIso)

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
  combine-fwd (suc m) {n} {v = x ∷ v} = S.trans S.+-comm S.+-lunit , combine-fwd m {n}

  F-preserve-products : FPF.preserve-chosen-products FD.products
                          (biproducts→products SM.cmon-enriched SM.biproduct)
  F-preserve-products {m} {n} .IsIso.inverse = combine {m} {n}
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id .*≈* ._≈s_.func-eq {u₁ , w₁} {u₂ , w₂} (u≈ , w≈) =
    FD.≈ᵥ-trans (FD.+ᵥ-cong (FD.vtake-++ {m} {n} {u₁} {w₁}) FD.≈ᵥ-refl) (FD.≈ᵥ-trans FD.+ᵥ-runit u≈) ,
    FD.≈ᵥ-trans (FD.+ᵥ-cong FD.≈ᵥ-refl (FD.vdrop-++ {m} {n} {u₁} {w₁})) (FD.≈ᵥ-trans FD.+ᵥ-lunit w≈)
  F-preserve-products {m} {n} .IsIso.inverse∘f≈id .*≈* ._≈s_.func-eq {v} v≈ =
    FD.≈ᵥ-trans (combine-fwd m {n} {v}) v≈

------------------------------------------------------------------------------
-- For S a (bounded) distributive lattice (join +, meet ·), each free object
-- fobj n is a self-dual distributive lattice, so the conjugate embedding
-- (semimodule.DistributiveLattice.to-conj) applies.
module DistribLattices {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where
  open import Data.Nat using (ℕ; zero; suc)
  open import basics using (IsPreorder; IsMeet; IsTop)
  open import meet-semilattice using (MeetSemilattice)
  import semimodule

  open Mat S using ([]; _∷_; Vec; εᵥ; _+ᵥ_; _≈ᵥ_; ≈ᵥ-refl; ≈ᵥ-trans; ≈ᵥ-sym; +ᵥ-runit; +ᵥ-lunit; +ᵥ-cong; scale-εᵥ; scale)
  open semimodule S using (module S; 𝕀; module DistributiveLattice; _⇒_; _≈m_; _∘_; Dual; cat)
  open _⇒_
  open _≈m_
  open Embedding S using (fobj)
  open import prop-setoid using () renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
  open Category cat using (Iso)

  module DistribLattice
    (∧-idem    : ∀ {x} → S._≈_ (S._·_ x x) x)
    (⊤-add-top : ∀ {x} → S._≈_ (S._+_ S.ι x) S.ι)
    where
    module DL = DistributiveLattice ∧-idem ⊤-add-top

    ----------------------------------------------------------------------------
    -- S as a distributive lattice: the meet · is the lattice meet of the join order.
    private
      module Scalar where
        open CommutativeSemiring S using (_≈_; refl; sym; trans; ε-annihilᵣ)
          renaming ( _·_ to _∧_ ; _+_ to _∨_ ; ε to ⊥ ; ι to ⊤
                   ; ·-cong to ∧-cong ; ·-comm to ∧-comm ; ·-assoc to ∧-assoc ; ·-lunit to ∧-lunit
                   ; +-cong to ∨-cong ; +-comm to ∨-comm ; +-assoc to ∨-assoc ; +-lunit to ∨-lunit
                   ; +-interchange to ∨-interchange
                   ; ·-+-distribₗ to ∧-∨-distribₗ ; ·-+-distribᵣ to ∧-∨-distribᵣ ) public
        open IsPreorder (DL.≤-isPreorder 𝕀) using () renaming (refl to ≤-refl; trans to ≤-trans)

        ∨-∧-absorption : ∀ {a b} → a ∨ (a ∧ b) ≈ a
        ∨-∧-absorption =
          trans (∨-cong (trans (sym ∧-lunit) ∧-comm) refl)
                (trans (sym ∧-∨-distribₗ) (trans (∧-cong refl ⊤-add-top) (trans ∧-comm ∧-lunit)))

        ∧-monoʳ : ∀ {a b c} → DL._≤_ 𝕀 a b → DL._≤_ 𝕀 (c ∧ a) (c ∧ b)
        ∧-monoʳ a≤b = trans (sym ∧-∨-distribₗ) (∧-cong refl a≤b)

        ∧-monoˡ : ∀ {a b c} → DL._≤_ 𝕀 a b → DL._≤_ 𝕀 (a ∧ c) (b ∧ c)
        ∧-monoˡ a≤b = trans (sym ∧-∨-distribᵣ) (∧-cong a≤b refl)

        ∧-isMeet : IsMeet (DL.≤-isPreorder 𝕀) _∧_
        ∧-isMeet .IsMeet.π₁ = trans ∨-comm ∨-∧-absorption
        ∧-isMeet .IsMeet.π₂ = trans (∨-cong ∧-comm refl) (trans ∨-comm ∨-∧-absorption)
        ∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z =
          ≤-trans (trans (∨-cong (sym ∧-idem) refl) (∧-monoʳ x≤z)) (∧-monoˡ x≤y)

        ⊤-isTop : IsTop (DL.≤-isPreorder 𝕀) ⊤
        ⊤-isTop .IsTop.≤-top = trans ∨-comm ⊤-add-top

        ∧-∨-distrib : ∀ {a b c} → DL._≤_ 𝕀 (a ∧ (b ∨ c)) ((a ∧ b) ∨ (a ∧ c))
        ∧-∨-distrib = DL.≈→≤ 𝕀 ∧-∨-distribₗ

        -- The join is zero-sum-free: a ∨ b ≈ ⊥ iff both are ⊥.
        ∨-idem : ∀ {a} → (a ∨ a) ≈ a
        ∨-idem = DL.+-idem 𝕀

        ∨-runit : ∀ {a} → (a ∨ ⊥) ≈ a
        ∨-runit = trans ∨-comm ∨-lunit

        ∨-≈⊥ₗ : ∀ {a b} → (a ∨ b) ≈ ⊥ → a ≈ ⊥
        ∨-≈⊥ₗ a∨b≈⊥ =
          trans (sym ∨-runit)
            (trans (∨-cong refl (sym a∨b≈⊥))
              (trans (sym ∨-assoc) (trans (∨-cong ∨-idem refl) a∨b≈⊥)))

        ∨-≈⊥ᵣ : ∀ {a b} → (a ∨ b) ≈ ⊥ → b ≈ ⊥
        ∨-≈⊥ᵣ a∨b≈⊥ = ∨-≈⊥ₗ (trans ∨-comm a∨b≈⊥)

        ⊥-∨ : ∀ {a b} → a ≈ ⊥ → b ≈ ⊥ → (a ∨ b) ≈ ⊥
        ⊥-∨ a≈⊥ b≈⊥ = trans (∨-cong a≈⊥ b≈⊥) ∨-lunit

        -- Dot product ⟪ x , y ⟫ = ⋁ᵢ (xᵢ ∧ yᵢ).
        ⟪_,_⟫ : ∀ {n} → Vec n → Vec n → S.Carrier
        ⟪ []    , []    ⟫ = ⊥
        ⟪ x ∷ u , y ∷ v ⟫ = (x ∧ y) ∨ ⟪ u , v ⟫

        -- The dot product is a symmetric bilinear form.
        ⟪⟫-comm : ∀ {n} {a b : Vec n} → ⟪ a , b ⟫ ≈ ⟪ b , a ⟫
        ⟪⟫-comm {a = []}    {[]}    = refl
        ⟪⟫-comm {a = _ ∷ u} {_ ∷ v} = ∨-cong ∧-comm (⟪⟫-comm {a = u} {v})

        ⟪⟫-resp-≈ : ∀ {n} {a a' b b' : Vec n} → a ≈ᵥ a' → b ≈ᵥ b' → ⟪ a , b ⟫ ≈ ⟪ a' , b' ⟫
        ⟪⟫-resp-≈ {a = []}    {[]}    {[]}    {[]}    _        _        = refl
        ⟪⟫-resp-≈ {a = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} (p , ps) (q , qs) = ∨-cong (∧-cong p q) (⟪⟫-resp-≈ ps qs)

        ⟪⟫-ε₂ : ∀ {n} {a : Vec n} → ⟪ a , εᵥ ⟫ ≈ ⊥
        ⟪⟫-ε₂ {a = []}    = refl
        ⟪⟫-ε₂ {a = _ ∷ u} = ⊥-∨ ε-annihilᵣ (⟪⟫-ε₂ {a = u})

        ⟪⟫-+₂ : ∀ {n} {a b b' : Vec n} → ⟪ a , b +ᵥ b' ⟫ ≈ (⟪ a , b ⟫ ∨ ⟪ a , b' ⟫)
        ⟪⟫-+₂ {a = []}    {[]}    {[]}    = sym ∨-lunit
        ⟪⟫-+₂ {a = _ ∷ u} {b = _ ∷ v} {b' = _ ∷ v'} =
          trans (∨-cong ∧-∨-distribₗ (⟪⟫-+₂ {a = u} {v} {v'})) ∨-interchange

        ⟪⟫-·₂ : ∀ {n} {s} {a b : Vec n} → ⟪ a , scale s b ⟫ ≈ (s ∧ ⟪ a , b ⟫)
        ⟪⟫-·₂ {a = []}    {b = []}    = sym ε-annihilᵣ
        ⟪⟫-·₂ {a = _ ∷ u} {b = _ ∷ v} =
          trans (∨-cong (trans (∧-cong refl ∧-comm) (trans (sym ∧-assoc) ∧-comm)) (⟪⟫-·₂ {a = u} {v})) (sym ∧-∨-distribₗ)

    open Scalar using (⟪_,_⟫; _≈_; ⊥; refl; sym; trans; ∨-cong; ∧-cong; ∨-≈⊥ₗ; ∨-≈⊥ᵣ; ⊥-∨
                      ; ∧-comm; ∧-lunit; ∨-lunit; ∨-runit; ε-annihilᵣ
                      ; ⟪⟫-comm; ⟪⟫-resp-≈; ⟪⟫-ε₂; ⟪⟫-+₂; ⟪⟫-·₂)

    ----------------------------------------------------------------------------
    -- Pointwise lift of the meet to fobj n.

    _∧_ : ∀ {n} → Vec n → Vec n → Vec n
    []      ∧ []      = []
    (x ∷ u) ∧ (y ∷ v) = (x Scalar.∧ y) ∷ (u ∧ v)

    ⊤ : ∀ {n} → Vec n
    ⊤ {zero}  = []
    ⊤ {suc n} = Scalar.⊤ ∷ ⊤

    π₁ : ∀ {n} {u v : Vec n} → DL._≤_ (fobj n) (u ∧ v) u
    π₁ {u = []}    {[]}    = tt
    π₁ {u = _ ∷ _} {_ ∷ _} = Scalar.∧-isMeet .IsMeet.π₁ , π₁

    π₂ : ∀ {n} {u v : Vec n} → DL._≤_ (fobj n) (u ∧ v) v
    π₂ {u = []}    {[]}    = tt
    π₂ {u = _ ∷ _} {_ ∷ _} = Scalar.∧-isMeet .IsMeet.π₂ , π₂

    ⟨_,_⟩ : ∀ {n} {u v w : Vec n} → DL._≤_ (fobj n) u v → DL._≤_ (fobj n) u w → DL._≤_ (fobj n) u (v ∧ w)
    ⟨_,_⟩ {u = []}    {[]}    {[]}    _           _           = tt
    ⟨_,_⟩ {u = _ ∷ _} {_ ∷ _} {_ ∷ _} (u≤v , u≤v') (u≤w , u≤w') =
      Scalar.∧-isMeet .IsMeet.⟨_,_⟩ u≤v u≤w , ⟨ u≤v' , u≤w' ⟩

    ⊤-top : ∀ {n} {u : Vec n} → DL._≤_ (fobj n) u ⊤
    ⊤-top {u = []}    = tt
    ⊤-top {u = _ ∷ _} = Scalar.⊤-isTop .IsTop.≤-top , ⊤-top

    ∧-∨-distrib : ∀ {n} (u v w : Vec n) →
                  DL._≤_ (fobj n) (u ∧ (v +ᵥ w)) ((u ∧ v) +ᵥ (u ∧ w))
    ∧-∨-distrib []      []      []      = tt
    ∧-∨-distrib (x ∷ u) (y ∷ v) (z ∷ w) = Scalar.∧-∨-distrib , ∧-∨-distrib u v w

    meets : ∀ n → MeetSemilattice (DL.preorder (fobj n))
    meets n .MeetSemilattice._∧_                    = _∧_
    meets n .MeetSemilattice.⊤                      = ⊤
    meets n .MeetSemilattice.∧-isMeet .IsMeet.π₁    = π₁
    meets n .MeetSemilattice.∧-isMeet .IsMeet.π₂    = π₂
    meets n .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ = ⟨_,_⟩
    meets n .MeetSemilattice.⊤-isTop .IsTop.≤-top   = ⊤-top

    ----------------------------------------------------------------------------
    -- Disjointness aligns with the dot product: x # y iff ⟪ x , y ⟫ ≈ ⊥.

    align-core : ∀ {n} {a b : Vec n} → ((a ∧ b) ≈ᵥ εᵥ) ⇔ (⟪ a , b ⟫ ≈ ⊥)
    align-core {a = []}    {[]}    .proj₁ _       = refl
    align-core {a = []}    {[]}    .proj₂ _       = tt
    align-core {a = _ ∷ _} {_ ∷ _} .proj₁ (h , t) = ⊥-∨ h (align-core .proj₁ t)
    align-core {a = _ ∷ _} {_ ∷ _} .proj₂ p       = ∨-≈⊥ₗ p , align-core .proj₂ (∨-≈⊥ᵣ p)

    align : ∀ {n} {a b : Vec n} → DL._≤_ (fobj n) (a ∧ b) εᵥ ⇔ (⟪ a , b ⟫ ≈ ⊥)
    align {a = a} {b} .proj₁ h = align-core {a = a} {b} .proj₁ (≈ᵥ-trans (≈ᵥ-sym +ᵥ-runit) h)
    align {a = a} {b} .proj₂ q = ≈ᵥ-trans +ᵥ-runit (align-core {a = a} {b} .proj₂ q)

    -- Reconstruct a vector from a functional (linear map to a scalar): weights f = (f e₀ , f e₁ , …).
    weights : ∀ {n} → (Vec n → S.Carrier) → Vec n
    weights {zero}  f = []
    weights {suc n} f = f (S.ι ∷ εᵥ) ∷ weights (λ w → f (S.ε ∷ w))

    weights-resp : ∀ {n} {f g : Vec n → S.Carrier} → (∀ w → f w ≈ g w) → weights f ≈ᵥ weights g
    weights-resp {zero}  f≈g = tt
    weights-resp {suc n} f≈g = f≈g (S.ι ∷ εᵥ) , weights-resp (λ w → f≈g (S.ε ∷ w))

    weights-ε : ∀ {n} → weights {n} (λ _ → S.ε) ≈ᵥ εᵥ
    weights-ε {zero}  = tt
    weights-ε {suc n} = refl , weights-ε

    weights-+ : ∀ {n} {f g : Vec n → S.Carrier} → weights (λ w → f w S.+ g w) ≈ᵥ (weights f +ᵥ weights g)
    weights-+ {zero}  = tt
    weights-+ {suc n} {f} {g} = refl , weights-+ {f = λ w → f (S.ε ∷ w)} {g = λ w → g (S.ε ∷ w)}

    weights-· : ∀ {n} {s} {f : Vec n → S.Carrier} → weights (λ w → s S.· f w) ≈ᵥ scale s (weights f)
    weights-· {zero}  = tt
    weights-· {suc n} {s} {f} = refl , weights-· {f = λ w → f (S.ε ∷ w)}

    -- weights recovers a vector from the measurement it induces.
    weights-fwd : ∀ {n} (a : Vec n) → weights (λ b → ⟪ a , b ⟫) ≈ᵥ a
    weights-fwd []       = tt
    weights-fwd (x ∷ xs) =
        trans (∨-cong (trans ∧-comm ∧-lunit) (⟪⟫-ε₂ {a = xs})) ∨-runit
      , ≈ᵥ-trans (weights-resp (λ w → trans (∨-cong ε-annihilᵣ refl) ∨-lunit)) (weights-fwd xs)

    shift : ∀ {n} → fobj n ⇒ fobj (suc n)
    shift .*→* ._⇒s_.func w = S.ε ∷ w
    shift .*→* ._⇒s_.func-resp-≈ w≈w' = refl , w≈w'
    shift .preserve-ze = ≈ᵥ-refl
    shift .preserve-+ = sym ∨-lunit , ≈ᵥ-refl
    shift .preserve-· = sym ε-annihilᵣ , ≈ᵥ-refl

    -- Decompose a vector into its first basis component plus the tail below a zero head.
    decomp : ∀ {n} (b₀ : S.Carrier) (bs : Vec n) → (b₀ ∷ bs) ≈ᵥ (scale b₀ (S.ι ∷ εᵥ) +ᵥ (S.ε ∷ bs))
    decomp b₀ bs .proj₁ = sym (trans ∨-runit (trans ∧-comm ∧-lunit))
    decomp b₀ bs .proj₂ = ≈ᵥ-sym (≈ᵥ-trans (+ᵥ-cong scale-εᵥ ≈ᵥ-refl) +ᵥ-lunit)

    -- Measurement induced by weights φ agrees with φ.
    eval-weights : ∀ {n} (φ : fobj n ⇒ 𝕀) (b : Vec n) → ⟪ weights (φ .func) , b ⟫ ≈ φ .func b
    eval-weights {zero}  φ []        = sym (φ .preserve-ze)
    eval-weights {suc n} φ (b₀ ∷ bs) =
      trans (∨-cong refl (eval-weights (φ ∘ shift) bs))
            (trans (∨-cong ∧-comm refl)
                   (sym (trans (φ .func-resp-≈ (decomp b₀ bs))
                               (trans (φ .preserve-+) (∨-cong (φ .preserve-·) refl)))))

    ----------------------------------------------------------------------------
    -- Self-duality: fwd a = (b ↦ ⟪ a , b ⟫), so pairing reduces to ⟪_,_⟫.

    self-dual : ∀ n → Iso (fobj n) (Dual (fobj n))
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func b = ⟪ a , b ⟫
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func-resp-≈ b≈b' = ⟪⟫-resp-≈ {a = a} ≈ᵥ-refl b≈b'
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .preserve-ze = ⟪⟫-ε₂ {a = a}
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .preserve-+ = ⟪⟫-+₂ {a = a}
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .preserve-· = ⟪⟫-·₂ {a = a}
    self-dual n .Iso.fwd .*→* ._⇒s_.func-resp-≈ a≈a' .*≈* ._≈s_.func-eq b≈b' = ⟪⟫-resp-≈ a≈a' b≈b'
    self-dual n .Iso.fwd .preserve-ze .*≈* ._≈s_.func-eq {b} _ =
      trans (⟪⟫-comm {a = εᵥ} {b}) (⟪⟫-ε₂ {a = b})
    self-dual n .Iso.fwd .preserve-+ {a₁} {a₂} .*≈* ._≈s_.func-eq {b} {b'} b≈b' =
      trans (⟪⟫-resp-≈ {a = a₁ +ᵥ a₂} ≈ᵥ-refl b≈b')
        (trans (⟪⟫-comm {a = a₁ +ᵥ a₂} {b'})
          (trans (⟪⟫-+₂ {a = b'} {a₁} {a₂}) (∨-cong (⟪⟫-comm {a = b'} {a₁}) (⟪⟫-comm {a = b'} {a₂}))))
    self-dual n .Iso.fwd .preserve-· {s} {a} .*≈* ._≈s_.func-eq {b} {b'} b≈b' =
      trans (⟪⟫-resp-≈ {a = scale s a} ≈ᵥ-refl b≈b')
        (trans (⟪⟫-comm {a = scale s a} {b'})
          (trans (⟪⟫-·₂ {s = s} {a = b'} {a}) (∧-cong refl (⟪⟫-comm {a = b'} {a}))))

    self-dual n .Iso.bwd .*→* ._⇒s_.func φ = weights (φ .func)
    self-dual n .Iso.bwd .*→* ._⇒s_.func-resp-≈ φ≈φ' = weights-resp (λ w → φ≈φ' .*≈* ._≈s_.func-eq (≈ᵥ-refl {v = w}))
    self-dual n .Iso.bwd .preserve-ze = weights-ε
    self-dual n .Iso.bwd .preserve-+ {φ} {φ'} = weights-+ {f = φ .func} {g = φ' .func}
    self-dual n .Iso.bwd .preserve-· {s} {φ} = weights-· {f = φ .func}
    self-dual n .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq {φ} φ≈φ' .*≈* ._≈s_.func-eq {b} b≈b' =
      trans (eval-weights φ b) (φ≈φ' .*≈* ._≈s_.func-eq b≈b')
    self-dual n .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq {a} a≈a' = ≈ᵥ-trans (weights-fwd a) a≈a'

    -- Each S-vector is a self-dual distributive lattice, so the LatConj embedding DistributiveLattice.to-conj
    -- applies to S-matrices.

    freeSDL : ℕ → DL.SelfDualLattice
    freeSDL n .DL.SelfDualLattice.M           = fobj n
    freeSDL n .DL.SelfDualLattice.self-dual   = self-dual n
    freeSDL n .DL.SelfDualLattice.meets       = meets n
    freeSDL n .DL.SelfDualLattice.∧-∨-distrib = ∧-∨-distrib
    freeSDL n .DL.SelfDualLattice.align       = align
