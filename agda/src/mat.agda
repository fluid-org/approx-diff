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
  F .Functor.fmor-cong {f₂ = f₂} f₁≈f₂ .*≈* ._≈s_.func-eq u≈v =
    FD.≈-trans (f₁≈f₂ _) (f₂ .FD.func-resp-≈ u≈v)
  F .Functor.fmor-id .*≈* ._≈s_.func-eq u≈v = u≈v
  F .Functor.fmor-comp f g .*≈* ._≈s_.func-eq u≈v =
    f .FD.func-resp-≈ (g .FD.func-resp-≈ u≈v)

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

  F-preserve-products : FPF.preserve-chosen-products FD.products
                          (biproducts→products SM.cmon-enriched SM.biproduct)
  F-preserve-products {m} {n} .IsIso.inverse = combine {m} {n}
  F-preserve-products {m} {n} .IsIso.f∘inverse≈id .*≈* ._≈s_.func-eq {u₁ , w₁} {u₂ , w₂} (u≈ , w≈) =
    FD.≈-trans (FD.+-cong (FD.vtake-++ {m} {n} {u₁} {w₁}) FD.≈-refl) (FD.≈-trans FD.+-runit u≈) ,
    FD.≈-trans (FD.+-cong FD.≈-refl (FD.vdrop-++ {m} {n} {u₁} {w₁})) (FD.≈-trans FD.+-lunit w≈)
  F-preserve-products {m} {n} .IsIso.inverse∘f≈id .*≈* ._≈s_.func-eq {v} v≈ =
    FD.≈-trans (combine-fwd m {n} {v}) v≈

------------------------------------------------------------------------------
-- For S a (bounded) distributive lattice (join +, meet ·), each free object
-- fobj n is a self-dual distributive lattice, so the conjugate embedding
-- (semimodule.JoinSemilattices.to-conj) applies.
module DistribLattices {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where
  open import Data.Nat using (ℕ; zero; suc)
  open import basics using (IsPreorder; IsMeet; IsTop)
  open import meet-semilattice using (MeetSemilattice)
  import semimodule

  open Mat S using ([]; _∷_; Vec; ε; _+_; _≈_; ≈-refl; ≈-trans; ≈-sym; +-runit; +-lunit; +-cong; scale-ε; scale)
  open semimodule S using (module S; 𝕀; module JoinSemilattices; _⇒_; _≈m_; _∘_; Dual; cat)
  open _⇒_
  open _≈m_
  open Embedding S using (fobj)
  open import prop-setoid using () renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
  open Category cat using (Iso)

  module DistribLattice
    (∧-idem    : ∀ {x} → S._≈_ (S._·_ x x) x)
    (⊤-add-top : ∀ {x} → S._≈_ (S._+_ S.ι x) S.ι)
    where
    open JoinSemilattices ⊤-add-top

    ----------------------------------------------------------------------------
    -- S as a distributive lattice: the meet · is the lattice meet of the join order.
    private
      module Scalar where
        open CommutativeSemiring S using (refl; sym; trans; ε-annihilᵣ)
          renaming ( _·_ to _∧_ ; _+_ to _∨_ ; ε to ⊥ ; ι to ⊤
                   ; ·-cong to ∧-cong ; ·-comm to ∧-comm ; ·-assoc to ∧-assoc ; ·-lunit to ∧-lunit
                   ; +-cong to ∨-cong ; +-comm to ∨-comm ; +-assoc to ∨-assoc ; +-lunit to ∨-lunit
                   ; +-interchange to ∨-interchange
                   ; ·-+-distribₗ to ∧-∨-distribₗ ; ·-+-distribᵣ to ∧-∨-distribᵣ ) public
        open IsPreorder (≤-isPreorder 𝕀) using () renaming (refl to ≤-refl; trans to ≤-trans)

        ∨-∧-absorption : ∀ {a b} → a ∨ (a ∧ b) S.≈ a
        ∨-∧-absorption =
          trans (∨-cong (trans (sym ∧-lunit) ∧-comm) refl)
                (trans (sym ∧-∨-distribₗ) (trans (∧-cong refl ⊤-add-top) (trans ∧-comm ∧-lunit)))

        ∧-monoʳ : ∀ {a b c} → _≤_ 𝕀 a b → _≤_ 𝕀 (c ∧ a) (c ∧ b)
        ∧-monoʳ a≤b = trans (sym ∧-∨-distribₗ) (∧-cong refl a≤b)

        ∧-monoˡ : ∀ {a b c} → _≤_ 𝕀 a b → _≤_ 𝕀 (a ∧ c) (b ∧ c)
        ∧-monoˡ a≤b = trans (sym ∧-∨-distribᵣ) (∧-cong a≤b refl)

        ∧-isMeet : IsMeet (≤-isPreorder 𝕀) _∧_
        ∧-isMeet .IsMeet.π₁ = trans ∨-comm ∨-∧-absorption
        ∧-isMeet .IsMeet.π₂ = trans (∨-cong ∧-comm refl) (trans ∨-comm ∨-∧-absorption)
        ∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z =
          ≤-trans (trans (∨-cong (sym ∧-idem) refl) (∧-monoʳ x≤z)) (∧-monoˡ x≤y)

        ⊤-isTop : IsTop (≤-isPreorder 𝕀) ⊤
        ⊤-isTop .IsTop.≤-top = trans ∨-comm ⊤-add-top

        ∧-∨-distrib : ∀ {a b c} → _≤_ 𝕀 (a ∧ (b ∨ c)) ((a ∧ b) ∨ (a ∧ c))
        ∧-∨-distrib = ≈→≤ 𝕀 ∧-∨-distribₗ

        -- The join is zero-sum-free: a ∨ b ≈ ⊥ iff both are ⊥.
        ∨-idem : ∀ {a} → (a ∨ a) S.≈ a
        ∨-idem = +-idem 𝕀

        ∨-runit : ∀ {a} → (a ∨ ⊥) S.≈ a
        ∨-runit = trans ∨-comm ∨-lunit

        ∨-≈⊥ₗ : ∀ {a b} → (a ∨ b) S.≈ ⊥ → a S.≈ ⊥
        ∨-≈⊥ₗ a∨b≈⊥ =
          trans (sym ∨-runit)
            (trans (∨-cong refl (sym a∨b≈⊥))
              (trans (sym ∨-assoc) (trans (∨-cong ∨-idem refl) a∨b≈⊥)))

        ∨-≈⊥ᵣ : ∀ {a b} → (a ∨ b) S.≈ ⊥ → b S.≈ ⊥
        ∨-≈⊥ᵣ a∨b≈⊥ = ∨-≈⊥ₗ (trans ∨-comm a∨b≈⊥)

        ⊥-∨ : ∀ {a b} → a S.≈ ⊥ → b S.≈ ⊥ → (a ∨ b) S.≈ ⊥
        ⊥-∨ a≈⊥ b≈⊥ = trans (∨-cong a≈⊥ b≈⊥) ∨-lunit

        -- Dot product ⟪ x , y ⟫ = ⋁ᵢ (xᵢ ∧ yᵢ).
        ⟪_,_⟫ : ∀ {n} → Vec n → Vec n → S.Carrier
        ⟪ []    , []    ⟫ = ⊥
        ⟪ x ∷ u , y ∷ v ⟫ = (x ∧ y) ∨ ⟪ u , v ⟫

        -- The dot product is a symmetric bilinear form.
        ⟪⟫-comm : ∀ {n} {a b : Vec n} → ⟪ a , b ⟫ S.≈ ⟪ b , a ⟫
        ⟪⟫-comm {a = []}    {[]}    = refl
        ⟪⟫-comm {a = _ ∷ u} {_ ∷ v} = ∨-cong ∧-comm (⟪⟫-comm {a = u} {v})

        ⟪⟫-resp-≈ : ∀ {n} {a a' b b' : Vec n} → a ≈ a' → b ≈ b' → ⟪ a , b ⟫ S.≈ ⟪ a' , b' ⟫
        ⟪⟫-resp-≈ {a = []}    {[]}    {[]}    {[]}    _        _        = refl
        ⟪⟫-resp-≈ {a = _ ∷ _} {_ ∷ _} {_ ∷ _} {_ ∷ _} (p , ps) (q , qs) = ∨-cong (∧-cong p q) (⟪⟫-resp-≈ ps qs)

        ⟪⟫-ε₂ : ∀ {n} {a : Vec n} → ⟪ a , ε ⟫ S.≈ ⊥
        ⟪⟫-ε₂ {a = []}    = refl
        ⟪⟫-ε₂ {a = _ ∷ u} = ⊥-∨ ε-annihilᵣ (⟪⟫-ε₂ {a = u})

        ⟪⟫-+₂ : ∀ {n} {a b b' : Vec n} → ⟪ a , b + b' ⟫ S.≈ (⟪ a , b ⟫ ∨ ⟪ a , b' ⟫)
        ⟪⟫-+₂ {a = []}    {[]}    {[]}    = sym ∨-lunit
        ⟪⟫-+₂ {a = _ ∷ u} {b = _ ∷ v} {b' = _ ∷ v'} =
          trans (∨-cong ∧-∨-distribₗ (⟪⟫-+₂ {a = u} {v} {v'})) ∨-interchange

        ⟪⟫-·₂ : ∀ {n} {s} {a b : Vec n} → ⟪ a , scale s b ⟫ S.≈ (s ∧ ⟪ a , b ⟫)
        ⟪⟫-·₂ {a = []}    {b = []}    = sym ε-annihilᵣ
        ⟪⟫-·₂ {a = _ ∷ u} {b = _ ∷ v} =
          trans (∨-cong (trans (∧-cong refl ∧-comm) (trans (sym ∧-assoc) ∧-comm)) (⟪⟫-·₂ {a = u} {v})) (sym ∧-∨-distribₗ)

    open Scalar using (⟪_,_⟫; ⊥; refl; sym; trans; ∨-cong; ∧-cong; ∨-≈⊥ₗ; ∨-≈⊥ᵣ; ⊥-∨; ∧-comm; ∧-lunit; ∨-lunit;
                       ∨-runit; ε-annihilᵣ; ⟪⟫-comm; ⟪⟫-resp-≈; ⟪⟫-ε₂; ⟪⟫-+₂; ⟪⟫-·₂)

    ----------------------------------------------------------------------------
    -- Pointwise lift of the meet to fobj n.

    _∧_ : ∀ {n} → Vec n → Vec n → Vec n
    []      ∧ []      = []
    (x ∷ u) ∧ (y ∷ v) = (x Scalar.∧ y) ∷ (u ∧ v)

    ⊤ : ∀ {n} → Vec n
    ⊤ {zero}  = []
    ⊤ {suc n} = Scalar.⊤ ∷ ⊤

    π₁ : ∀ {n} {u v : Vec n} → _≤_ (fobj n) (u ∧ v) u
    π₁ {u = []}    {[]}    = tt
    π₁ {u = _ ∷ _} {_ ∷ _} = Scalar.∧-isMeet .IsMeet.π₁ , π₁

    π₂ : ∀ {n} {u v : Vec n} → _≤_ (fobj n) (u ∧ v) v
    π₂ {u = []}    {[]}    = tt
    π₂ {u = _ ∷ _} {_ ∷ _} = Scalar.∧-isMeet .IsMeet.π₂ , π₂

    ⟨_,_⟩ : ∀ {n} {u v w : Vec n} → _≤_ (fobj n) u v → _≤_ (fobj n) u w → _≤_ (fobj n) u (v ∧ w)
    ⟨_,_⟩ {u = []}    {[]}    {[]}    _           _           = tt
    ⟨_,_⟩ {u = _ ∷ _} {_ ∷ _} {_ ∷ _} (u≤v , u≤v') (u≤w , u≤w') =
      Scalar.∧-isMeet .IsMeet.⟨_,_⟩ u≤v u≤w , ⟨ u≤v' , u≤w' ⟩

    ⊤-top : ∀ {n} {u : Vec n} → _≤_ (fobj n) u ⊤
    ⊤-top {u = []}    = tt
    ⊤-top {u = _ ∷ _} = Scalar.⊤-isTop .IsTop.≤-top , ⊤-top

    ∧-∨-distrib : ∀ {n} (u v w : Vec n) →
                  _≤_ (fobj n) (u ∧ (v + w)) ((u ∧ v) + (u ∧ w))
    ∧-∨-distrib []      []      []      = tt
    ∧-∨-distrib (x ∷ u) (y ∷ v) (z ∷ w) = Scalar.∧-∨-distrib , ∧-∨-distrib u v w

    meets : ∀ n → MeetSemilattice (preorder (fobj n))
    meets n .MeetSemilattice._∧_                    = _∧_
    meets n .MeetSemilattice.⊤                      = ⊤
    meets n .MeetSemilattice.∧-isMeet .IsMeet.π₁    = π₁
    meets n .MeetSemilattice.∧-isMeet .IsMeet.π₂    = π₂
    meets n .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ = ⟨_,_⟩
    meets n .MeetSemilattice.⊤-isTop .IsTop.≤-top   = ⊤-top

    ----------------------------------------------------------------------------
    -- Disjointness aligns with the dot product: x # y iff ⟪ x , y ⟫ ≈ ⊥.

    align-core : ∀ {n} {a b : Vec n} → ((a ∧ b) ≈ ε) ⇔ (⟪ a , b ⟫ S.≈ ⊥)
    align-core {a = []}    {[]}    .proj₁ _       = refl
    align-core {a = []}    {[]}    .proj₂ _       = tt
    align-core {a = _ ∷ _} {_ ∷ _} .proj₁ (h , t) = ⊥-∨ h (align-core .proj₁ t)
    align-core {a = _ ∷ _} {_ ∷ _} .proj₂ p       = ∨-≈⊥ₗ p , align-core .proj₂ (∨-≈⊥ᵣ p)

    align : ∀ {n} {a b : Vec n} → _≤_ (fobj n) (a ∧ b) ε ⇔ (⟪ a , b ⟫ S.≈ ⊥)
    align {a = a} {b} .proj₁ h = align-core {a = a} {b} .proj₁ (≈-trans (≈-sym +-runit) h)
    align {a = a} {b} .proj₂ q = ≈-trans +-runit (align-core {a = a} {b} .proj₂ q)

    -- Reconstruct a vector from a functional (linear map to a scalar): weights f = (f e₀ , f e₁ , …).
    weights : ∀ {n} → (Vec n → S.Carrier) → Vec n
    weights {zero}  f = []
    weights {suc n} f = f (S.ι ∷ ε) ∷ weights (λ w → f (S.ε ∷ w))

    weights-resp : ∀ {n} {f g : Vec n → S.Carrier} → (∀ w → f w S.≈ g w) → weights f ≈ weights g
    weights-resp {zero}  f≈g = tt
    weights-resp {suc n} f≈g = f≈g (S.ι ∷ ε) , weights-resp (λ w → f≈g (S.ε ∷ w))

    weights-ε : ∀ {n} → weights {n} (λ _ → S.ε) ≈ ε
    weights-ε {zero}  = tt
    weights-ε {suc n} = refl , weights-ε

    weights-+ : ∀ {n} {f g : Vec n → S.Carrier} → weights (λ w → f w S.+ g w) ≈ (weights f + weights g)
    weights-+ {zero}  = tt
    weights-+ {suc n} {f} {g} = refl , weights-+ {f = λ w → f (S.ε ∷ w)} {g = λ w → g (S.ε ∷ w)}

    weights-· : ∀ {n} {s} {f : Vec n → S.Carrier} → weights (λ w → s S.· f w) ≈ scale s (weights f)
    weights-· {zero}  = tt
    weights-· {suc n} {s} {f} = refl , weights-· {f = λ w → f (S.ε ∷ w)}

    -- weights recovers a vector from the measurement it induces.
    weights-fwd : ∀ {n} (a : Vec n) → weights (λ b → ⟪ a , b ⟫) ≈ a
    weights-fwd []       = tt
    weights-fwd (x ∷ xs) =
        trans (∨-cong (trans ∧-comm ∧-lunit) (⟪⟫-ε₂ {a = xs})) ∨-runit
      , ≈-trans (weights-resp (λ w → trans (∨-cong ε-annihilᵣ refl) ∨-lunit)) (weights-fwd xs)

    shift : ∀ {n} → fobj n ⇒ fobj (suc n)
    shift .*→* ._⇒s_.func w = S.ε ∷ w
    shift .*→* ._⇒s_.func-resp-≈ w≈w' = refl , w≈w'
    shift .preserve-ze = ≈-refl
    shift .preserve-+ = sym ∨-lunit , ≈-refl
    shift .preserve-· = sym ε-annihilᵣ , ≈-refl

    -- Decompose a vector into its first basis component plus the tail below a zero head.
    decomp : ∀ {n} (b₀ : S.Carrier) (bs : Vec n) → (b₀ ∷ bs) ≈ (scale b₀ (S.ι ∷ ε) + (S.ε ∷ bs))
    decomp b₀ bs .proj₁ = sym (trans ∨-runit (trans ∧-comm ∧-lunit))
    decomp b₀ bs .proj₂ = ≈-sym (≈-trans (+-cong scale-ε ≈-refl) +-lunit)

    -- Measurement induced by weights φ agrees with φ.
    eval-weights : ∀ {n} (φ : fobj n ⇒ 𝕀) (b : Vec n) → ⟪ weights (φ .func) , b ⟫ S.≈ φ .func b
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
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .*→* ._⇒s_.func-resp-≈ b≈b' = ⟪⟫-resp-≈ {a = a} ≈-refl b≈b'
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .preserve-ze = ⟪⟫-ε₂ {a = a}
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .preserve-+ = ⟪⟫-+₂ {a = a}
    self-dual n .Iso.fwd .*→* ._⇒s_.func a .preserve-· = ⟪⟫-·₂ {a = a}
    self-dual n .Iso.fwd .*→* ._⇒s_.func-resp-≈ a≈a' .*≈* ._≈s_.func-eq b≈b' = ⟪⟫-resp-≈ a≈a' b≈b'
    self-dual n .Iso.fwd .preserve-ze .*≈* ._≈s_.func-eq {b} _ =
      trans (⟪⟫-comm {a = ε} {b}) (⟪⟫-ε₂ {a = b})
    self-dual n .Iso.fwd .preserve-+ {a₁} {a₂} .*≈* ._≈s_.func-eq {b} {b'} b≈b' =
      trans (⟪⟫-resp-≈ {a = a₁ + a₂} ≈-refl b≈b')
        (trans (⟪⟫-comm {a = a₁ + a₂} {b'})
          (trans (⟪⟫-+₂ {a = b'} {a₁} {a₂}) (∨-cong (⟪⟫-comm {a = b'} {a₁}) (⟪⟫-comm {a = b'} {a₂}))))
    self-dual n .Iso.fwd .preserve-· {s} {a} .*≈* ._≈s_.func-eq {b} {b'} b≈b' =
      trans (⟪⟫-resp-≈ {a = scale s a} ≈-refl b≈b')
        (trans (⟪⟫-comm {a = scale s a} {b'})
          (trans (⟪⟫-·₂ {s = s} {a = b'} {a}) (∧-cong refl (⟪⟫-comm {a = b'} {a}))))

    self-dual n .Iso.bwd .*→* ._⇒s_.func φ = weights (φ .func)
    self-dual n .Iso.bwd .*→* ._⇒s_.func-resp-≈ φ≈φ' = weights-resp (λ w → φ≈φ' .*≈* ._≈s_.func-eq (≈-refl {v = w}))
    self-dual n .Iso.bwd .preserve-ze = weights-ε
    self-dual n .Iso.bwd .preserve-+ {φ} {φ'} = weights-+ {f = φ .func} {g = φ' .func}
    self-dual n .Iso.bwd .preserve-· {s} {φ} = weights-· {f = φ .func}
    self-dual n .Iso.fwd∘bwd≈id .*≈* ._≈s_.func-eq {φ} φ≈φ' .*≈* ._≈s_.func-eq {b} b≈b' =
      trans (eval-weights φ b) (φ≈φ' .*≈* ._≈s_.func-eq b≈b')
    self-dual n .Iso.bwd∘fwd≈id .*≈* ._≈s_.func-eq {a} a≈a' = ≈-trans (weights-fwd a) a≈a'

    -- Each S-vector is a self-dual distributive lattice, so the LatConj embedding applies to S-matrices.
    -- We don't actually use this; it's metatheory for the paper.
    vec-sddl : ℕ → SelfDualDistributiveLattice
    vec-sddl n .SelfDualDistributiveLattice.M           = fobj n
    vec-sddl n .SelfDualDistributiveLattice.self-dual   = self-dual n
    vec-sddl n .SelfDualDistributiveLattice.meets       = meets n
    vec-sddl n .SelfDualDistributiveLattice.∧-∨-distrib = ∧-∨-distrib
    vec-sddl n .SelfDualDistributiveLattice.align       = align
