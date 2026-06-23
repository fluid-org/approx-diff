{-# OPTIONS --postfix-projections --prop --safe #-}

module matrix-new where

open import Level using (0ℓ; _⊔_)
open import prop using (tt; _,_; proj₁; proj₂; _⇔_; sym-⇔; trans-⇔)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category)

-- Free finitely-generated S-semimodules ("matrices"), with vectors as Data.Vec (instead of functions
-- Fin n → Carrier).
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
  infix 4 _≈_
  _≈_ : ∀ {n} → Vec n → Vec n → Prop ℓ
  []      ≈ []      = ⊤
  (x ∷ u) ≈ (y ∷ v) = (x S.≈ y) ∧ (u ≈ v)

  ≈-refl : ∀ {n} {v : Vec n} → v ≈ v
  ≈-refl {v = []}    = tt
  ≈-refl {v = x ∷ v} = S.refl , ≈-refl

  ≈-sym : ∀ {n} {u v : Vec n} → u ≈ v → v ≈ u
  ≈-sym {u = []} {[]} _              = tt
  ≈-sym {u = _ ∷ _} {_ ∷ _} (p , q)  = S.sym p , ≈-sym q

  ≈-trans : ∀ {n} {u v w : Vec n} → u ≈ v → v ≈ w → u ≈ w
  ≈-trans {u = []} {[]} {[]} _ _                         = tt
  ≈-trans {u = _ ∷ _} {_ ∷ _} {_ ∷ _} (p , q) (p' , q')  = S.trans p p' , ≈-trans q q'

  -- Zero vector.
  ε : ∀ {n} → Vec n
  ε {zero}  = []
  ε {suc n} = S.ε ∷ ε

  -- Pointwise addition and scalar multiplication.
  infixl 20 _+_
  _+_ : ∀ {n} → Vec n → Vec n → Vec n
  _+_ = V.zipWith S._+_

  scale : ∀ {n} → S.Carrier → Vec n → Vec n
  scale a = V.map (a S.·_)

  ----------------------------------------------------------------------------
  -- Morphisms: linear maps S^n → S^m.

  record _⇒_ (n m : ℕ) : Set (o ⊔ ℓ) where
    no-eta-equality
    field
      func             : Vec n → Vec m
      func-resp-≈      : ∀ {u v} → u ≈ v → func u ≈ func v
      +-preserving     : ∀ {u v} → func (u + v) ≈ (func u + func v)
      ε-preserving     : func ε ≈ ε
      scale-preserving : ∀ {a v} → func (scale a v) ≈ scale a (func v)
  open _⇒_ public

  infix 4 _≃_
  _≃_ : ∀ {n m} → n ⇒ m → n ⇒ m → Prop (o ⊔ ℓ)
  f ≃ g = ∀ v → f .func v ≈ g .func v

  ≃-isEquiv : ∀ {n m} → IsEquivalence (_≃_ {n} {m})
  ≃-isEquiv .IsEquivalence.refl v = ≈-refl
  ≃-isEquiv .IsEquivalence.sym f≃g v = ≈-sym (f≃g v)
  ≃-isEquiv .IsEquivalence.trans f≃g g≃h v = ≈-trans (f≃g v) (g≃h v)

  ----------------------------------------------------------------------------
  -- Category of free semimodules.

  id : ∀ {n} → n ⇒ n
  id .func v = v
  id .func-resp-≈ u≈ = u≈
  id .+-preserving = ≈-refl
  id .ε-preserving = ≈-refl
  id .scale-preserving = ≈-refl

  infixl 21 _∘_
  _∘_ : ∀ {n m k} → m ⇒ k → n ⇒ m → n ⇒ k
  (g ∘ f) .func v = g .func (f .func v)
  (g ∘ f) .func-resp-≈ u≈ = g .func-resp-≈ (f .func-resp-≈ u≈)
  (g ∘ f) .+-preserving = ≈-trans (g .func-resp-≈ (f .+-preserving)) (g .+-preserving)
  (g ∘ f) .ε-preserving = ≈-trans (g .func-resp-≈ (f .ε-preserving)) (g .ε-preserving)
  (g ∘ f) .scale-preserving = ≈-trans (g .func-resp-≈ (f .scale-preserving)) (g .scale-preserving)

  cat : Category _ _ _
  cat .Category.obj = ℕ
  cat .Category._⇒_ n m = n ⇒ m
  cat .Category._≈_ = _≃_
  cat .Category.isEquiv = ≃-isEquiv
  cat .Category.id n = id
  cat .Category._∘_ = _∘_
  cat .Category.∘-cong {f₁ = F₁} {g₂ = G₂} F≃ G≃ v = ≈-trans (F₁ .func-resp-≈ (G≃ v)) (F≃ (G₂ .func v))
  cat .Category.id-left _ = ≈-refl
  cat .Category.id-right _ = ≈-refl
  cat .Category.assoc _ _ _ _ = ≈-refl

  ----------------------------------------------------------------------------
  -- Vector algebra.

  []-≈ : ∀ (w : Vec 0) → ε ≈ w
  []-≈ [] = tt

  +-cong : ∀ {n} {u u' v v' : Vec n} → u ≈ u' → v ≈ v' → (u + v) ≈ (u' + v')
  +-cong {u = []} {[]} {[]} {[]} _ _ = tt
  +-cong {u = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} (p , q) (p' , q') = S.+-cong p p' , +-cong q q'

  +-lunit : ∀ {n} {v : Vec n} → (ε + v) ≈ v
  +-lunit {v = []} = tt
  +-lunit {v = x ∷ v} = S.+-lunit , +-lunit

  +-assoc : ∀ {n} {u v w : Vec n} → ((u + v) + w) ≈ (u + (v + w))
  +-assoc {u = []} {[]} {[]} = tt
  +-assoc {u = _ ∷ _} {_ ∷ _} {_ ∷ _} = S.+-assoc , +-assoc

  +-comm : ∀ {n} {u v : Vec n} → (u + v) ≈ (v + u)
  +-comm {u = []} {[]} = tt
  +-comm {u = _ ∷ _} {_ ∷ _} = S.+-comm , +-comm

  +-interchange : ∀ {n} {a b c d : Vec n} → ((a + b) + (c + d)) ≈ ((a + c) + (b + d))
  +-interchange {a = []} {[]} {[]} {[]} = tt
  +-interchange {a = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} = S.+-interchange , +-interchange

  scale-ε : ∀ {n} {a} → scale a (ε {n}) ≈ ε
  scale-ε {zero}  = tt
  scale-ε {suc n} = S.ε-annihilᵣ , scale-ε

  scale-+ : ∀ {n} {a} {u v : Vec n} → scale a (u + v) ≈ (scale a u + scale a v)
  scale-+ {u = []} {[]} = tt
  scale-+ {u = _ ∷ _} {_ ∷ _} = S.·-+-distribₗ , scale-+

  +-runit : ∀ {n} {v : Vec n} → (v + ε) ≈ v
  +-runit {v = []}    = tt
  +-runit {v = x ∷ v} = S.trans S.+-comm S.+-lunit , +-runit

  scale-cong : ∀ {n} {a a'} {u v : Vec n} → a S.≈ a' → u ≈ v → scale a u ≈ scale a' v
  scale-cong {u = []}    {[]}    _  _       = tt
  scale-cong {u = _ ∷ _} {_ ∷ _} a≈ (p , q) = S.·-cong a≈ p , scale-cong a≈ q

  scale-+ₗ : ∀ {n} {a b} {v : Vec n} → scale (a S.+ b) v ≈ (scale a v + scale b v)
  scale-+ₗ {v = []}    = tt
  scale-+ₗ {v = _ ∷ _} = S.·-+-distribᵣ , scale-+ₗ

  scale-· : ∀ {n} {a b} {v : Vec n} → scale (a S.· b) v ≈ scale a (scale b v)
  scale-· {v = []}    = tt
  scale-· {v = _ ∷ _} = S.·-assoc , scale-·

  scale-ι : ∀ {n} {v : Vec n} → scale S.ι v ≈ v
  scale-ι {v = []}    = tt
  scale-ι {v = _ ∷ _} = S.·-lunit , scale-ι

  scale-0ₗ : ∀ {n} {v : Vec n} → scale S.ε v ≈ ε
  scale-0ₗ {v = []}    = tt
  scale-0ₗ {v = _ ∷ _} = S.ε-annihilₗ , scale-0ₗ

  open import Data.Nat using () renaming (_+_ to _+ℕ_)
  open V using (_++_)

  ++-cong : ∀ {m n} {u u' : Vec m} {v v' : Vec n} → u ≈ u' → v ≈ v' → (u ++ v) ≈ (u' ++ v')
  ++-cong {u = []}    {[]}    _        q = q
  ++-cong {u = _ ∷ _} {_ ∷ _} (p , ps) q = p , ++-cong ps q

  ++-+ : ∀ {m n} {u u' : Vec m} {v v' : Vec n} →
          ((u + u') ++ (v + v')) ≈ ((u ++ v) + (u' ++ v'))
  ++-+ {u = []}    {[]}                              = ≈-refl
  ++-+ {u = _ ∷ _} {_ ∷ _} {v = v} {v' = v'}        = S.refl , ++-+ {v = v} {v' = v'}

  ++-scale : ∀ {m n} {a} {u : Vec m} {v : Vec n} → scale a (u ++ v) ≈ (scale a u ++ scale a v)
  ++-scale {u = []}                  = ≈-refl
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
  terminal .is-terminal .to-terminal-ext f v = []-≈ (f .func v)

  initial : HasInitial cat
  initial .witness = 0
  initial .is-initial .from-initial .func _ = ε
  initial .is-initial .from-initial .func-resp-≈ _ = ≈-refl
  initial .is-initial .from-initial .+-preserving = ≈-sym +-lunit
  initial .is-initial .from-initial .ε-preserving = ≈-refl
  initial .is-initial .from-initial .scale-preserving = ≈-sym scale-ε
  initial .is-initial .from-initial-ext f [] = ≈-sym (f .ε-preserving)

  ----------------------------------------------------------------------------
  -- CMon-enrichment.

  open import cmon-enriched using (CMonEnriched)
  open import commutative-monoid using (CommutativeMonoid)
  open CMonEnriched

  εₘ : ∀ {n m} → n ⇒ m
  εₘ .func _ = ε
  εₘ .func-resp-≈ _ = ≈-refl
  εₘ .+-preserving = ≈-sym +-lunit
  εₘ .ε-preserving = ≈-refl
  εₘ .scale-preserving = ≈-sym scale-ε

  infixl 21 _+ₘ_
  _+ₘ_ : ∀ {n m} → n ⇒ m → n ⇒ m → n ⇒ m
  (f +ₘ g) .func v = f .func v + g .func v
  (f +ₘ g) .func-resp-≈ p = +-cong (f .func-resp-≈ p) (g .func-resp-≈ p)
  (f +ₘ g) .+-preserving = ≈-trans (+-cong (f .+-preserving) (g .+-preserving)) +-interchange
  (f +ₘ g) .ε-preserving = ≈-trans (+-cong (f .ε-preserving) (g .ε-preserving)) +-lunit
  (f +ₘ g) .scale-preserving = ≈-trans (+-cong (f .scale-preserving) (g .scale-preserving)) (≈-sym scale-+)

  cmon : CMonEnriched cat
  cmon .homCM n m .CommutativeMonoid.ε = εₘ
  cmon .homCM n m .CommutativeMonoid._+_ = _+ₘ_
  cmon .homCM n m .CommutativeMonoid.+-cong p q v = +-cong (p v) (q v)
  cmon .homCM n m .CommutativeMonoid.+-lunit v = +-lunit
  cmon .homCM n m .CommutativeMonoid.+-assoc v = +-assoc
  cmon .homCM n m .CommutativeMonoid.+-comm v = +-comm
  cmon .comp-bilinear₁ f₁ f₂ g v = ≈-refl
  cmon .comp-bilinear₂ f g₁ g₂ v = f .+-preserving
  cmon .comp-bilinear-ε₁ f v = ≈-refl
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

  vtake-cong : ∀ m {n} {u v : Vec (m +ℕ n)} → u ≈ v → vtake m u ≈ vtake m v
  vtake-cong zero _ = tt
  vtake-cong (suc m) {u = _ ∷ _} {_ ∷ _} (p , q) = p , vtake-cong m q

  vdrop-cong : ∀ m {n} {u v : Vec (m +ℕ n)} → u ≈ v → vdrop m u ≈ vdrop m v
  vdrop-cong zero p = p
  vdrop-cong (suc m) {u = _ ∷ _} {_ ∷ _} (_ , q) = vdrop-cong m q

  vtake-ε : ∀ m {n} → vtake m (ε {m +ℕ n}) ≈ ε
  vtake-ε zero    = tt
  vtake-ε (suc m) = S.refl , vtake-ε m

  vdrop-ε : ∀ m {n} → vdrop m (ε {m +ℕ n}) ≈ ε {n}
  vdrop-ε zero    = ≈-refl
  vdrop-ε (suc m) = vdrop-ε m

  vtake-+ : ∀ m {n} {u v : Vec (m +ℕ n)} → vtake m (u + v) ≈ (vtake m u + vtake m v)
  vtake-+ zero = tt
  vtake-+ (suc m) {u = _ ∷ _} {_ ∷ _} = S.refl , vtake-+ m

  vdrop-+ : ∀ m {n} {u v : Vec (m +ℕ n)} → vdrop m (u + v) ≈ (vdrop m u + vdrop m v)
  vdrop-+ zero = ≈-refl
  vdrop-+ (suc m) {u = _ ∷ _} {_ ∷ _} = vdrop-+ m

  vtake-scale : ∀ m {n} {a} {v : Vec (m +ℕ n)} → vtake m (scale a v) ≈ scale a (vtake m v)
  vtake-scale zero = tt
  vtake-scale (suc m) {v = _ ∷ _} = S.refl , vtake-scale m

  vdrop-scale : ∀ m {n} {a} {v : Vec (m +ℕ n)} → vdrop m (scale a v) ≈ scale a (vdrop m v)
  vdrop-scale zero = ≈-refl
  vdrop-scale (suc m) {v = _ ∷ _} = vdrop-scale m

  ++-ε : ∀ {m n} → (ε {m} ++ ε {n}) ≈ ε {m +ℕ n}
  ++-ε {zero}      = ≈-refl
  ++-ε {suc m} {n} = S.refl , ++-ε {m} {n}

  vtake-++ : ∀ {m n} {u : Vec m} {v : Vec n} → vtake m (u ++ v) ≈ u
  vtake-++ {u = []}    = tt
  vtake-++ {u = _ ∷ _} = S.refl , vtake-++

  vdrop-++ : ∀ {m n} {u : Vec m} {v : Vec n} → vdrop m (u ++ v) ≈ v
  vdrop-++ {u = []} = ≈-refl
  vdrop-++ {m = suc m} {n = n} {u = _ ∷ _} = vdrop-++ {m = m} {n = n}

  in₁-cong : ∀ {m n} {u v : Vec m} → u ≈ v → (u ++ ε {n}) ≈ (v ++ ε)
  in₁-cong {u = []} {[]}_ = ≈-refl
  in₁-cong {u = _ ∷ _} {_ ∷ _} (p , q) = p , in₁-cong q

  in₁-+ : ∀ {m n} {u v : Vec m} → ((u + v) ++ ε {n}) ≈ ((u ++ ε) + (v ++ ε))
  in₁-+ {u = []} {[]} = ≈-sym +-lunit
  in₁-+ {n = n} {u = _ ∷ _} {_ ∷ _} = S.refl , in₁-+ {n = n}

  in₁-scale : ∀ {m n} {a} {v : Vec m} → ((scale a v) ++ ε {n}) ≈ scale a (v ++ ε)
  in₁-scale {v = []}            = ≈-sym scale-ε
  in₁-scale {n = n} {v = _ ∷ _} = S.refl , in₁-scale {n = n}

  in₂-cong : ∀ {m n} {u v : Vec n} → u ≈ v → (ε {m} ++ u) ≈ (ε ++ v)
  in₂-cong {m = zero}  p = p
  in₂-cong {m = suc m} p = S.refl , in₂-cong p

  in₂-+ : ∀ {m n} {u v : Vec n} → (ε {m} ++ (u + v)) ≈ ((ε ++ u) + (ε ++ v))
  in₂-+ {m = zero}            = ≈-refl
  in₂-+ {m = suc m} {n = n}   = S.sym S.+-lunit , in₂-+ {n = n}

  in₂-scale : ∀ {m n} {a} {v : Vec n} → (ε {m} ++ scale a v) ≈ scale a (ε {m} ++ v)
  in₂-scale {m = zero}            = ≈-refl
  in₂-scale {m = suc m} {n = n}   = S.sym S.ε-annihilᵣ , in₂-scale {n = n}

  id-+-lem : ∀ m {n} {v : Vec (m +ℕ n)} → (((vtake m v) ++ ε {n}) + (ε {m} ++ (vdrop m v))) ≈ v
  id-+-lem zero                = +-lunit
  id-+-lem (suc m) {v = x ∷ v} = S.trans S.+-comm S.+-lunit , id-+-lem m

  -- Projections / injections.
  p₁ : ∀ {m n} → (m +ℕ n) ⇒ m
  p₁ {m} .func = vtake m
  p₁ {m} .func-resp-≈ = vtake-cong m
  p₁ {m} .+-preserving = vtake-+ m
  p₁ {m} .ε-preserving = vtake-ε m
  p₁ {m} .scale-preserving = vtake-scale m

  p₂ : ∀ {m n} → (m +ℕ n) ⇒ n
  p₂ {m} .func = vdrop m
  p₂ {m} .func-resp-≈ = vdrop-cong m
  p₂ {m} .+-preserving = vdrop-+ m
  p₂ {m} .ε-preserving = vdrop-ε m
  p₂ {m} .scale-preserving = vdrop-scale m

  in₁ : ∀ {m n} → m ⇒ (m +ℕ n)
  in₁ {m} {n} .func v = v ++ ε {n}
  in₁ {m} {n} .func-resp-≈ = in₁-cong {m} {n}
  in₁ {m} {n} .+-preserving = in₁-+ {m} {n}
  in₁ {m} {n} .ε-preserving = ++-ε {m} {n}
  in₁ {m} {n} .scale-preserving = in₁-scale {m} {n}

  in₂ : ∀ {m n} → n ⇒ (m +ℕ n)
  in₂ {m} {n} .func v = ε {m} ++ v
  in₂ {m} {n} .func-resp-≈ = in₂-cong {m} {n}
  in₂ {m} {n} .+-preserving = in₂-+ {m} {n}
  in₂ {m} {n} .ε-preserving = ++-ε {m} {n}
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
  fobj n .Semimodule.setoid .Setoid._≈_ = FD._≈_
  fobj n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.refl = FD.≈-refl
  fobj n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.sym = FD.≈-sym
  fobj n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.trans = FD.≈-trans
  fobj n .Semimodule.additive .CommutativeMonoid.ε = FD.ε
  fobj n .Semimodule.additive .CommutativeMonoid._+_ = FD._+_
  fobj n .Semimodule.additive .CommutativeMonoid.+-cong = FD.+-cong
  fobj n .Semimodule.additive .CommutativeMonoid.+-lunit = FD.+-lunit
  fobj n .Semimodule.additive .CommutativeMonoid.+-assoc = FD.+-assoc
  fobj n .Semimodule.additive .CommutativeMonoid.+-comm = FD.+-comm
  fobj n .Semimodule._·_ = FD.scale
  fobj n .Semimodule.·-cong = FD.scale-cong
  fobj n .Semimodule.·-mul = FD.scale-·
  fobj n .Semimodule.·-unit = FD.scale-ι
  fobj n .Semimodule.+-distribʳ = FD.scale-+ₗ
  fobj n .Semimodule.+-distribˡ = FD.scale-+
  fobj n .Semimodule.zero-distribʳ = FD.scale-0ₗ
  fobj n .Semimodule.zero-distribˡ = FD.scale-ε

  F : Functor FD.cat SM.cat
  F .Functor.fobj = fobj
  F .Functor.fmor f .*→* ._⇒s_.func = f .FD.func
  F .Functor.fmor f .*→* ._⇒s_.func-resp-≈ = f .FD.func-resp-≈
  F .Functor.fmor f .preserve-ze = f .FD.ε-preserving
  F .Functor.fmor f .preserve-+ = f .FD.+-preserving
  F .Functor.fmor f .preserve-· = f .FD.scale-preserving
  F .Functor.fmor-cong {f₂ = f₂} f₁≈f₂ .*≈* ._≈s_.func-eq u≈v = FD.≈-trans (f₁≈f₂ _) (f₂ .FD.func-resp-≈ u≈v)
  F .Functor.fmor-id .*≈* ._≈s_.func-eq u≈v = u≈v
  F .Functor.fmor-comp f g .*≈* ._≈s_.func-eq u≈v = f .FD.func-resp-≈ (g .FD.func-resp-≈ u≈v)

  module FPF = finite-product-functor F

  ----------------------------------------------------------------------------
  -- Terminal preservation: fobj 0 (the one-point Vec 0) is isomorphic to 𝟘.

  term-inv : 𝟘 ⇒ fobj 0
  term-inv .*→* ._⇒s_.func _ = FD.ε
  term-inv .*→* ._⇒s_.func-resp-≈ _ = FD.≈-refl
  term-inv .preserve-ze = FD.≈-refl
  term-inv .preserve-+ = FD.≈-refl
  term-inv .preserve-· = FD.≈-refl

  F-preserve-terminal : FPF.preserve-chosen-terminal FD.terminal SM.terminal
  F-preserve-terminal .IsIso.inverse = term-inv
  F-preserve-terminal .IsIso.f∘inverse≈id .*≈* ._≈s_.func-eq _ = tt
  F-preserve-terminal .IsIso.inverse∘f≈id .*≈* ._≈s_.func-eq {_} {v} _ = FD.[]-≈ v

  ----------------------------------------------------------------------------
  -- Product preservation: fobj (m + n) ≅ fobj m ⊕ fobj n, the inverse being _++_.

  combine : ∀ {m n} → (fobj m ⊕ fobj n) ⇒ fobj (m +ℕ n)
  combine .*→* ._⇒s_.func (u , w) = u ++ w
  combine .*→* ._⇒s_.func-resp-≈ (u≈ , w≈) = FD.++-cong u≈ w≈
  combine {m} {n} .preserve-ze = FD.++-ε {m} {n}
  combine {m} {n} .preserve-+ {u , w} {u' , w'} = FD.++-+ {u = u} {u'} {w} {w'}
  combine {m} {n} .preserve-· {a} {u , w} = FD.≈-sym (FD.++-scale {u = u} {w})

  -- combine ∘ fwd ≈ id, by recursion on the split point.  The biproduct-derived
  -- pairing adds ε on each side, hence the + ε / ε + terms.
  combine-fwd : ∀ m {n} {v : FD.Vec (m +ℕ n)} →
                ((FD.vtake m v FD.+ FD.ε) ++ (FD.ε FD.+ FD.vdrop m v)) FD.≈ v
  combine-fwd zero                    = FD.+-lunit
  combine-fwd (suc m) {n} {v = x ∷ v} = S.trans S.+-comm S.+-lunit , combine-fwd m {n}

  F-preserve-products : FPF.preserve-chosen-products FD.products (biproducts→products SM.cmon-enriched SM.biproduct)
  F-preserve-products {m} {n} .IsIso.inverse = combine {m} {n}
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id .*≈* ._≈s_.func-eq {u₁ , w₁} {u₂ , w₂} (u≈ , w≈) =
    FD.≈-trans (FD.+-cong (FD.vtake-++ {m} {n} {u₁} {w₁}) FD.≈-refl) (FD.≈-trans FD.+-runit u≈) ,
    FD.≈-trans (FD.+-cong FD.≈-refl (FD.vdrop-++ {m} {n} {u₁} {w₁})) (FD.≈-trans FD.+-lunit w≈)
  F-preserve-products {m} {n} .IsIso.inverse∘f≈id .*≈* ._≈s_.func-eq {v} v≈ =
    FD.≈-trans (combine-fwd m {n} {v}) v≈

  open Category SM.cat using (Iso; IsIso→Iso; Iso-trans; Iso-refl)
  open import prop using (tt)

  -- Each free object Sⁿ = fobj n is canonically self-dual: 𝕀's self-duality lifted through ⊕, transported
  -- along fobj(1+n) ≅ 𝕀 ⊕ fobj n.
  private
    dual-transport : ∀ {M N} → Iso M N → Iso N (Dual N) → Iso M (Dual M)
    dual-transport M≅N N≅N* = Iso-trans (Iso-trans M≅N N≅N*) (Dual-iso M≅N)

    fobj1≅𝕀 : Iso (fobj 1) 𝕀
    fobj1≅𝕀 .Iso.fwd .*→* ._⇒s_.func (x ∷ []) = x
    fobj1≅𝕀 .Iso.fwd .*→* ._⇒s_.func-resp-≈ {x ∷ []} {y ∷ []} (p , _) = p
    fobj1≅𝕀 .Iso.fwd .preserve-ze = S.refl
    fobj1≅𝕀 .Iso.fwd .preserve-+ {x ∷ []} {y ∷ []} = S.refl
    fobj1≅𝕀 .Iso.fwd .preserve-· {a} {x ∷ []} = S.refl
    fobj1≅𝕀 .Iso.bwd .*→* ._⇒s_.func x = x ∷ []
    fobj1≅𝕀 .Iso.bwd .*→* ._⇒s_.func-resp-≈ x≈y = x≈y , tt
    fobj1≅𝕀 .Iso.bwd .preserve-ze = S.refl , tt
    fobj1≅𝕀 .Iso.bwd .preserve-+ = S.refl , tt
    fobj1≅𝕀 .Iso.bwd .preserve-· = S.refl , tt
    fobj1≅𝕀 .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq x≈x' = x≈x'
    fobj1≅𝕀 .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq {x ∷ []} {y ∷ []} h = h

  fobj-sd : (n : ℕ) → SelfDual
  fobj-sd n .SelfDual.obj = fobj n
  fobj-sd zero .SelfDual.dual = dual-transport (IsIso→Iso F-preserve-terminal) (𝟘-sd .SelfDual.dual)
  fobj-sd (suc n) .SelfDual.dual =
    dual-transport (Iso-trans (IsIso→Iso (F-preserve-products {1} {n})) (⊕-iso fobj1≅𝕀 Iso-refl))
                   (⊕-sd 𝕀-sd (fobj-sd n) .SelfDual.dual)

------------------------------------------------------------------------------
-- For S a (bounded) distributive lattice (join +, meet ·), each free object fobj n is a self-dual
-- distributive lattice, so the conjugate embedding (semimodule.JoinSemilattices.to-conj) applies.
module DistribLattices {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where
  open import Data.Nat using (ℕ; zero; suc)
  import semimodule

  open Mat S using ([]; _∷_)
  open semimodule S using (module S; 𝕀; ⊕-iso; module JoinSemilattices; _⇒_; _≈m_; cat)
  open _⇒_
  open _≈m_
  open Embedding S using (fobj; F-preserve-terminal; F-preserve-products)
  open import prop-setoid using () renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
  open Category cat using (Iso; IsIso→Iso; Iso-trans)

  module DistribLattice
    (∧-idem    : ∀ {x} → S._≈_ (S._·_ x x) x)
    (⊤-add-top : ∀ {x} → S._≈_ (S._+_ S.ι x) S.ι)
    where
    open JoinSemilattices ⊤-add-top
    open JoinSemilattices.DistribLattices ⊤-add-top ∧-idem

    --------------------------------------------------------------------------
    -- An S-vector of length n is the n-ary biproduct of the unit.

    fobj1≅𝕀 : Iso (fobj 1) 𝕀
    fobj1≅𝕀 .Iso.fwd .*→* ._⇒s_.func (x ∷ []) = x
    fobj1≅𝕀 .Iso.fwd .*→* ._⇒s_.func-resp-≈ {x ∷ []} {y ∷ []} (p , _) = p
    fobj1≅𝕀 .Iso.fwd .preserve-ze = S.refl
    fobj1≅𝕀 .Iso.fwd .preserve-+ {x ∷ []} {y ∷ []} = S.refl
    fobj1≅𝕀 .Iso.fwd .preserve-· {a} {x ∷ []} = S.refl
    fobj1≅𝕀 .Iso.bwd .*→* ._⇒s_.func x = x ∷ []
    fobj1≅𝕀 .Iso.bwd .*→* ._⇒s_.func-resp-≈ x≈y = x≈y , tt
    fobj1≅𝕀 .Iso.bwd .preserve-ze = S.refl , tt
    fobj1≅𝕀 .Iso.bwd .preserve-+ = S.refl , tt
    fobj1≅𝕀 .Iso.bwd .preserve-· = S.refl , tt
    fobj1≅𝕀 .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq x≈x' = x≈x'
    fobj1≅𝕀 .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq {x ∷ []} {y ∷ []} h = h

    fobjⁿ≅⊕ⁿ𝕀 : ∀ n → Iso (fobj n) (SelfDualDistributiveLattice.obj (⊕ⁿ n))
    fobjⁿ≅⊕ⁿ𝕀 zero    = IsIso→Iso F-preserve-terminal
    fobjⁿ≅⊕ⁿ𝕀 (suc n) = Iso-trans (IsIso→Iso (F-preserve-products {1} {n})) (⊕-iso fobj1≅𝕀 (fobjⁿ≅⊕ⁿ𝕀 n))

    -- Each S-vector is a self-dual distributive lattice.
    vec-sddl : ℕ → SelfDualDistributiveLattice
    vec-sddl n = transport-sddl (⊕ⁿ n) (fobjⁿ≅⊕ⁿ𝕀 n)

    -- ...and, given a Boolean negation on the scalar, a BooleanSDDL (the n-vector negated pointwise).
    -- (⊕ⁿ-bsddl's lattice is ⊕ⁿ, but only up to the parallel recursion, so we transport the iso along it.)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

    private
      ⊕ⁿ-bsddl-sdl : (¬ : S.Carrier → S.Carrier)
                     (c-∧ : ∀ {x} → _≤_ 𝕀 (x S.· ¬ x) S.ε) (c-∨ : ∀ {x} → _≤_ 𝕀 S.ι (x S.+ ¬ x)) →
                     ∀ n → BooleanSDDL.selfDualLat (⊕ⁿ-bsddl ¬ c-∧ c-∨ n) ≡ ⊕ⁿ n
      ⊕ⁿ-bsddl-sdl ¬ c-∧ c-∨ zero    = refl
      ⊕ⁿ-bsddl-sdl ¬ c-∧ c-∨ (suc n) = cong (⊕-sddl 𝕀-sddl) (⊕ⁿ-bsddl-sdl ¬ c-∧ c-∨ n)

    vec-bsddl : (¬ : S.Carrier → S.Carrier)
                (complement-∧ : ∀ {x} → _≤_ 𝕀 (x S.· ¬ x) S.ε)
                (complement-∨ : ∀ {x} → _≤_ 𝕀 S.ι (x S.+ ¬ x)) →
                ℕ → BooleanSDDL
    vec-bsddl ¬ c-∧ c-∨ n =
      transport-bsddl (⊕ⁿ-bsddl ¬ c-∧ c-∨ n)
        (subst (λ s → Iso (fobj n) (SelfDualDistributiveLattice.obj s))
               (sym (⊕ⁿ-bsddl-sdl ¬ c-∧ c-∨ n)) (fobjⁿ≅⊕ⁿ𝕀 n))
