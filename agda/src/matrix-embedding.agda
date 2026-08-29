{-# OPTIONS --prop --postfix-projections --safe #-}

-- Mat(S) embedded in the semimodules, full and faithful: a dimension embeds as the semimodule of
-- weighted vectors over its positions, and a matrix as its action on them. This is the case X = 𝕀
-- of the embedding of Mat(End X) in any biproduct category, presented concretely so that a
-- morphism is read back from its values on the basis. The lifting on each side is the biproduct
-- with the unit object, and the comparison between the two splits a vector into its first entry
-- and the rest.
open import Level using (0ℓ)
open import Data.Nat as Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc)
open import prop using (∃ₛ; proj₁; proj₂) renaming (_,_ to _,ₚ_)
open import Data.Product using (_,_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; HasTerminal; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct; biproduct-iso; biproducts→products)
open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
import lifting
import matrix
import semimodule

module matrix-embedding {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where

open CommutativeSemiring S hiding (_≈_; refl; sym; trans)
open Setoid A

module M = matrix.Mat S
open M
  using (Matrix; Vec; Σ; I; εₘ; _+ₘ_; _≈ₘ_; Σ-cong; Σ-ε; Σ-+; Σ-unit;
         Σ-·-distribₗ; Σ-·-distribᵣ; Σ-interchange;
         ∘-cong; id-left; assoc; comp-bilinear₁; comp-bilinear₂;
         comp-bilinear-ε₁; comp-bilinear-ε₂;
         ⟨_,_⟩; _∥_; concat; split₁; split₂; Σ-p₁; Σ-p₂; Σ-in₁; Σ-in₂)
  renaming (_∘_ to _∘ₘ_)
module SemiMod = semimodule S
open SemiMod using (Semimodule; 𝕀)
open SemiMod._⇒_
open SemiMod._≈m_
open Functor
open Biproduct

private
  module SemiMod-cat = Category SemiMod.cat
  module M-cat = Category M.cat
  open CMonEnriched SemiMod.cmon-enriched using (_+m_; homCM; εm)

  +m-cong : ∀ {X Y : Semimodule} {f f' g g' : SemiMod._⇒_ X Y} →
            SemiMod-cat._≈_ f f' → SemiMod-cat._≈_ g g' →
            SemiMod-cat._≈_ (_+m_ f g) (_+m_ f' g')
  +m-cong = CommutativeMonoid.+-cong (homCM _ _)

------------------------------------------------------------------------------
-- The action of a matrix on a vector: composition with the vector as a single column.

col : ∀ {n} → Vec n → Matrix n 1
col v i _ = v i

app : ∀ {m n} → Matrix m n → Vec n → Vec m
app {m} {n} R v i = (R ∘ₘ col v) i zero

app-+ : ∀ {m n} (R : Matrix m n) (u v : Vec n) (i : Fin m) →
        app R (λ j → u j + v j) i ≈ (app R u i + app R v i)
app-+ R u v i = comp-bilinear₂ R (col u) (col v) i zero

app-· : ∀ {m n} (R : Matrix m n) (s : Setoid.Carrier A) (u : Vec n) (i : Fin m) →
        app R (λ j → s · u j) i ≈ (s · app R u i)
app-· {m} {n} R s u i =
  trans (Σ-cong {n} (λ j → trans (sym ·-assoc) (trans (·-cong ·-comm refl) ·-assoc)))
        (sym (Σ-·-distribₗ {n} s (λ j → R i j · u j)))

app-ε : ∀ {m n} (R : Matrix m n) (i : Fin m) → app R (λ _ → ε) i ≈ ε
app-ε {m} {n} R i = comp-bilinear-ε₂ {m} {n} {1} R i zero

app-congₘ : ∀ {m n} {R R' : Matrix m n} → R ≈ₘ R' → ∀ (v : Vec n) (i : Fin m) → app R v i ≈ app R' v i
app-congₘ {R = R} {R' = R'} h v i = ∘-cong {N₁ = col v} {N₂ = col v} h (λ _ _ → refl) i zero

app-congᵥ : ∀ {m n} (R : Matrix m n) {u w : Vec n} → (∀ j → u j ≈ w j) → ∀ (i : Fin m) → app R u i ≈ app R w i
app-congᵥ R {u = u} {w = w} h i =
  ∘-cong {M₁ = R} {M₂ = R} {N₁ = col u} {N₂ = col w} (λ _ _ → refl) (λ j _ → h j) i zero

app-∘ : ∀ {m n k} (R : Matrix m n) (T : Matrix n k) (v : Vec k) (i : Fin m) →
        app (R ∘ₘ T) v i ≈ app R (app T v) i
app-∘ R T v i = assoc R T (col v) i zero

app-+ₘ : ∀ {m n} (R T : Matrix m n) (v : Vec n) (i : Fin m) → app (R +ₘ T) v i ≈ (app R v i + app T v i)
app-+ₘ R T v i = comp-bilinear₁ R T (col v) i zero

app-I : ∀ {n} (v : Vec n) (i : Fin n) → app (I {n}) v i ≈ v i
app-I v i = id-left {M = col v} i zero

app-εₘ : ∀ {m n} (v : Vec n) (i : Fin m) → app (εₘ {m} {n}) v i ≈ ε
app-εₘ v i = comp-bilinear-ε₁ (col v) i zero

app-p₁ : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin x) → app (M.p₁ {x} {y}) w i ≈ split₁ {x} w i
app-p₁ = Σ-p₁

app-p₂ : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin y) → app (M.p₂ {x} {y}) w i ≈ split₂ {x} w i
app-p₂ = Σ-p₂

app-in₁ : ∀ {x y} (u : Vec x) (i : Fin (x +ℕ y)) → app (M.in₁ {x} {y}) u i ≈ concat {x} {y} u (λ _ → ε) i
app-in₁ = Σ-in₁

app-in₂ : ∀ {x y} (w : Vec y) (i : Fin (x +ℕ y)) → app (M.in₂ {x} {y}) w i ≈ concat {x} {y} (λ _ → ε) w i
app-in₂ = Σ-in₂

concat-+ : ∀ {x y} (u : Vec x) (w : Vec y) (i : Fin (x +ℕ y)) →
           (concat {x} {y} u (λ _ → ε) i + concat {x} {y} (λ _ → ε) w i) ≈ concat {x} {y} u w i
concat-+ {Nat.zero}  u w i       = +-lunit
concat-+ {Nat.suc x} u w zero    = +-runit
concat-+ {Nat.suc x} u w (suc i) = concat-+ {x} (λ j → u (suc j)) w i

app-pair : ∀ {m x y} (f : Matrix x m) (g : Matrix y m) (u : Vec m) (i : Fin (x +ℕ y)) →
           app ⟨ f , g ⟩ u i ≈ concat {x} {y} (app f u) (app g u) i
app-pair {m} {x} {y} f g u i =
  trans (app-+ₘ (M.in₁ {x} {y} ∘ₘ f) (M.in₂ {x} {y} ∘ₘ g) u i)
  (trans (+-cong (trans (app-∘ (M.in₁ {x} {y}) f u i) (app-in₁ (app f u) i))
                 (trans (app-∘ (M.in₂ {x} {y}) g u i) (app-in₂ (app g u) i)))
         (concat-+ (app f u) (app g u) i))

app-∥ : ∀ {m n k} (A : Matrix k m) (B : Matrix k n) (w : Vec (m +ℕ n)) (i : Fin k) →
        app (A ∥ B) w i ≈ (app A (split₁ {m} w) i + app B (split₂ {m} w) i)
app-∥ {m} {n} A B w i =
  trans (app-+ₘ (A ∘ₘ M.p₁ {m} {n}) (B ∘ₘ M.p₂ {m} {n}) w i)
        (+-cong (trans (app-∘ A (M.p₁ {m} {n}) w i) (app-congᵥ A (app-p₁ w) i))
                (trans (app-∘ B (M.p₂ {m} {n}) w i) (app-congᵥ B (app-p₂ w) i)))

------------------------------------------------------------------------------
-- The realisation: the semimodule of weighted vectors over the positions, pointwise.

𝔽 : ℕ → Semimodule
𝔽 n .Semimodule.setoid .Setoid.Carrier = Vec n
𝔽 n .Semimodule.setoid .Setoid._≈_ u v = ∀ i → u i ≈ v i
𝔽 n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.refl i = refl
𝔽 n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.sym e i = sym (e i)
𝔽 n .Semimodule.setoid .Setoid.isEquivalence .IsEquivalence.trans e e' i = trans (e i) (e' i)
𝔽 n .Semimodule.additive .CommutativeMonoid.ε _ = ε
𝔽 n .Semimodule.additive .CommutativeMonoid._+_ u v i = u i + v i
𝔽 n .Semimodule.additive .CommutativeMonoid.+-cong e e' i = +-cong (e i) (e' i)
𝔽 n .Semimodule.additive .CommutativeMonoid.+-lunit i = +-lunit
𝔽 n .Semimodule.additive .CommutativeMonoid.+-assoc i = +-assoc
𝔽 n .Semimodule.additive .CommutativeMonoid.+-comm i = +-comm
𝔽 n .Semimodule._·_ s u i = s · u i
𝔽 n .Semimodule.·-cong e e' i = ·-cong e (e' i)
𝔽 n .Semimodule.·-mul i = ·-assoc
𝔽 n .Semimodule.·-unit i = ·-lunit
𝔽 n .Semimodule.+-distribʳ i = ·-+-distribᵣ
𝔽 n .Semimodule.+-distribˡ i = ·-+-distribₗ
𝔽 n .Semimodule.zero-distribʳ i = ε-annihilₗ
𝔽 n .Semimodule.zero-distribˡ i = ε-annihilᵣ

mat : ∀ {m n} → Matrix m n → SemiMod._⇒_ (𝔽 n) (𝔽 m)
mat R .*→* .prop-setoid._⇒_.func = app R
mat R .*→* .prop-setoid._⇒_.func-resp-≈ = app-congᵥ R
mat R .preserve-ze = app-ε R
mat R .preserve-+ {u} {v} = app-+ R u v
mat R .preserve-· {s} {u} = app-· R s u

𝔽F : Functor M.cat SemiMod.cat
𝔽F .fobj = 𝔽
𝔽F .fmor = mat
𝔽F .fmor-cong {f₂ = R'} h .*≈* .prop-setoid._≃m_.func-eq {u} e i = trans (app-congₘ h u i) (app-congᵥ R' e i)
𝔽F .fmor-id .*≈* .prop-setoid._≃m_.func-eq {u} e i = trans (app-I u i) (e i)
𝔽F .fmor-comp f g .*≈* .prop-setoid._≃m_.func-eq {u} e i =
  trans (app-∘ f g u i) (app-congᵥ f (λ j → app-congᵥ g e j) i)

mat-cong : ∀ {m n} {R T : Matrix m n} → R ≈ₘ T → SemiMod-cat._≈_ (mat R) (mat T)
mat-cong h = 𝔽F .fmor-cong h

mat-comp : ∀ {m n k} (R : Matrix m n) (T : Matrix n k) →
           SemiMod-cat._≈_ (mat (R ∘ₘ T)) (SemiMod._∘_ (mat R) (mat T))
mat-comp R T = 𝔽F .fmor-comp R T

mat-I : ∀ {n} → SemiMod-cat._≈_ (mat (I {n})) (SemiMod.id (𝔽 n))
mat-I = 𝔽F .fmor-id

mat-ε : ∀ {m n} → SemiMod-cat._≈_ (mat (εₘ {m} {n})) (εm {𝔽 n} {𝔽 m})
mat-ε .*≈* .prop-setoid._≃m_.func-eq {u} e i = app-εₘ u i

mat-+ : ∀ {m n} (R T : Matrix m n) → SemiMod-cat._≈_ (mat (R +ₘ T)) (_+m_ (mat R) (mat T))
mat-+ R T .*≈* .prop-setoid._≃m_.func-eq {u} e i =
  trans (app-+ₘ R T u i) (+-cong (app-congᵥ R e i) (app-congᵥ T e i))

------------------------------------------------------------------------------
-- Preservation of the finite products: the biproduct of dimensions realises as a biproduct, with
-- the block matrices as its structure morphisms.

𝔽-biproduct : ∀ m n → Biproduct SemiMod.cmon-enriched (𝔽 m) (𝔽 n)
𝔽-biproduct m n .prod = 𝔽 (m +ℕ n)
𝔽-biproduct m n .p₁ = mat (M.p₁ {m} {n})
𝔽-biproduct m n .p₂ = mat (M.p₂ {m} {n})
𝔽-biproduct m n .in₁ = mat (M.in₁ {m} {n})
𝔽-biproduct m n .in₂ = mat (M.in₂ {m} {n})
𝔽-biproduct m n .id-1 =
  SemiMod-cat.≈-trans (SemiMod-cat.≈-sym (mat-comp (M.p₁ {m} {n}) (M.in₁ {m} {n})))
              (SemiMod-cat.≈-trans (mat-cong (M.id-1 m n)) mat-I)
𝔽-biproduct m n .id-2 =
  SemiMod-cat.≈-trans (SemiMod-cat.≈-sym (mat-comp (M.p₂ {m} {n}) (M.in₂ {m} {n})))
              (SemiMod-cat.≈-trans (mat-cong (M.id-2 m n)) mat-I)
𝔽-biproduct m n .zero-1 =
  SemiMod-cat.≈-trans (SemiMod-cat.≈-sym (mat-comp (M.p₁ {m} {n}) (M.in₂ {m} {n})))
              (SemiMod-cat.≈-trans (mat-cong (M.zero-1 m n)) mat-ε)
𝔽-biproduct m n .zero-2 =
  SemiMod-cat.≈-trans (SemiMod-cat.≈-sym (mat-comp (M.p₂ {m} {n}) (M.in₁ {m} {n})))
              (SemiMod-cat.≈-trans (mat-cong (M.zero-2 m n)) mat-ε)
𝔽-biproduct m n .id-+ =
  SemiMod-cat.≈-trans
    (+m-cong (SemiMod-cat.≈-sym (mat-comp (M.in₁ {m} {n}) (M.p₁ {m} {n})))
             (SemiMod-cat.≈-sym (mat-comp (M.in₂ {m} {n}) (M.p₂ {m} {n}))))
    (SemiMod-cat.≈-trans (SemiMod-cat.≈-sym (mat-+ (M.in₁ {m} {n} ∘ₘ M.p₁ {m} {n})
                                   (M.in₂ {m} {n} ∘ₘ M.p₂ {m} {n})))
                 (SemiMod-cat.≈-trans (mat-cong (M.id-+ m n)) mat-I))

𝔽F-preserve-products :
  preserve-chosen-products 𝔽F (biproducts→products M.cmon M.biproduct)
    (biproducts→products SemiMod.cmon-enriched SemiMod.biproduct)
𝔽F-preserve-products {m} {n} =
  biproduct-iso SemiMod.cmon-enriched (𝔽-biproduct m n) (SemiMod.biproduct (𝔽 m) (𝔽 n))

𝟘→𝔽0 : SemiMod._⇒_ SemiMod.𝟘 (𝔽 0)
𝟘→𝔽0 .*→* .prop-setoid._⇒_.func _ ()
𝟘→𝔽0 .*→* .prop-setoid._⇒_.func-resp-≈ _ ()
𝟘→𝔽0 .preserve-ze ()
𝟘→𝔽0 .preserve-+ ()
𝟘→𝔽0 .preserve-· ()

𝔽F-preserve-terminal : preserve-chosen-terminal 𝔽F M.terminal SemiMod.terminal
𝔽F-preserve-terminal .Category.IsIso.inverse = 𝟘→𝔽0
𝔽F-preserve-terminal .Category.IsIso.f∘inverse≈id =
  HasTerminal.to-terminal-unique SemiMod.terminal {x = SemiMod.𝟘} _ (SemiMod.id SemiMod.𝟘)
𝔽F-preserve-terminal .Category.IsIso.inverse∘f≈id .*≈* .prop-setoid._≃m_.func-eq _ ()

------------------------------------------------------------------------------
-- The two liftings: one fresh position on the position side, the scalars on the semimodule side.

module lifting-M = lifting M.cmon M.biproduct 1
module lifting-SemiMod = lifting SemiMod.cmon-enriched SemiMod.biproduct SemiMod.𝕀

ι1-fwd : SemiMod._⇒_ (𝔽 1) 𝕀
ι1-fwd .*→* .prop-setoid._⇒_.func v = v zero
ι1-fwd .*→* .prop-setoid._⇒_.func-resp-≈ e = e zero
ι1-fwd .preserve-ze = refl
ι1-fwd .preserve-+ = refl
ι1-fwd .preserve-· = refl

ι1-bwd : SemiMod._⇒_ 𝕀 (𝔽 1)
ι1-bwd .*→* .prop-setoid._⇒_.func a _ = a
ι1-bwd .*→* .prop-setoid._⇒_.func-resp-≈ e i = e
ι1-bwd .preserve-ze i = refl
ι1-bwd .preserve-+ i = refl
ι1-bwd .preserve-· i = refl

𝔽-L-fwd : ∀ n → SemiMod._⇒_ (𝔽 (lifting-M.L n)) (lifting-SemiMod.L (𝔽 n))
𝔽-L-fwd n .*→* .prop-setoid._⇒_.func v = v zero , λ k → v (suc k)
𝔽-L-fwd n .*→* .prop-setoid._⇒_.func-resp-≈ e = e zero ,ₚ λ k → e (suc k)
𝔽-L-fwd n .preserve-ze = refl ,ₚ λ k → refl
𝔽-L-fwd n .preserve-+ = refl ,ₚ λ k → refl
𝔽-L-fwd n .preserve-· = refl ,ₚ λ k → refl

𝔽-L-bwd : ∀ n → SemiMod._⇒_ (lifting-SemiMod.L (𝔽 n)) (𝔽 (lifting-M.L n))
𝔽-L-bwd n .*→* .prop-setoid._⇒_.func (a , u) zero = a
𝔽-L-bwd n .*→* .prop-setoid._⇒_.func (a , u) (suc k) = u k
𝔽-L-bwd n .*→* .prop-setoid._⇒_.func-resp-≈ e zero = e .proj₁
𝔽-L-bwd n .*→* .prop-setoid._⇒_.func-resp-≈ e (suc k) = e .proj₂ k
𝔽-L-bwd n .preserve-ze zero = refl
𝔽-L-bwd n .preserve-ze (suc k) = refl
𝔽-L-bwd n .preserve-+ zero = refl
𝔽-L-bwd n .preserve-+ (suc k) = refl
𝔽-L-bwd n .preserve-· zero = refl
𝔽-L-bwd n .preserve-· (suc k) = refl

𝔽-L-iso : ∀ n → Category.Iso SemiMod.cat (𝔽 (lifting-M.L n)) (lifting-SemiMod.L (𝔽 n))
𝔽-L-iso n .Category.Iso.fwd = 𝔽-L-fwd n
𝔽-L-iso n .Category.Iso.bwd = 𝔽-L-bwd n
𝔽-L-iso n .Category.Iso.fwd∘bwd≈id .*≈* .prop-setoid._≃m_.func-eq e = e
𝔽-L-iso n .Category.Iso.bwd∘fwd≈id .*≈* .prop-setoid._≃m_.func-eq e zero = e zero
𝔽-L-iso n .Category.Iso.bwd∘fwd≈id .*≈* .prop-setoid._≃m_.func-eq e (suc k) = e (suc k)

𝔽-L-natural : ∀ {P Q} (f : M-cat._⇒_ P Q) →
  SemiMod-cat._≈_ (SemiMod._∘_ (𝔽-L-fwd Q) (mat (lifting-M.Lmap f)))
          (SemiMod._∘_ (lifting-SemiMod.Lmap {𝔽 P} {𝔽 Q} (mat f)) (𝔽-L-fwd P))
𝔽-L-natural {P} {Q} f .*≈* .prop-setoid._≃m_.func-eq {u} {u'} e = root ,ₚ payload
  where
  root : app (lifting-M.Lmap f) u zero ≈ (u' zero + ε)
  root =
    trans (app-∥ (M.in₁ {1} {Q}) (M.in₂ {1} {Q} ∘ₘ f) u zero)
          (+-cong (trans (app-in₁ {1} {Q} (split₁ {1} u) zero) (e zero))
                  (trans (app-∘ (M.in₂ {1} {Q}) f (split₂ {1} u) zero)
                         (app-in₂ {1} {Q} (app f (split₂ {1} u)) zero)))

  payload : ∀ k → app (lifting-M.Lmap f) u (suc k) ≈ (ε + app f (λ l → u' (suc l)) k)
  payload k =
    trans (app-∥ (M.in₁ {1} {Q}) (M.in₂ {1} {Q} ∘ₘ f) u (suc k))
          (+-cong (app-in₁ {1} {Q} (split₁ {1} u) (suc k))
                  (trans (app-∘ (M.in₂ {1} {Q}) f (split₂ {1} u) (suc k))
                         (trans (app-in₂ {1} {Q} (app f (split₂ {1} u)) (suc k))
                                (app-congᵥ f (λ l → e (suc l)) k))))

------------------------------------------------------------------------------
-- The realisation is full and faithful: a linear map between free semimodules is the matrix of
-- its values on the basis, so a fibre map of the model is a weighted relation and nothing else.

app-e : ∀ {m n} (R : Matrix m n) (j : Fin n) (i : Fin m) → app R (M.e j) i ≈ R i j
app-e {m} {n} R j i = trans (Σ-cong {n} (λ l → ·-comm)) (Σ-unit j (λ l → R i l))

private
  shift : ∀ {m} → Vec m → Vec (Nat.suc m)
  shift u zero    = ε
  shift u (suc l) = u l

  shift-e : ∀ {m} (l : Fin m) (j : Fin (Nat.suc m)) → shift (M.e l) j ≈ M.e (suc l) j
  shift-e l zero     = refl
  shift-e l (suc j') = refl

  shift-map : ∀ {m n} → SemiMod._⇒_ (𝔽 (Nat.suc m)) (𝔽 n) → SemiMod._⇒_ (𝔽 m) (𝔽 n)
  shift-map k .*→* .prop-setoid._⇒_.func u = k .func (shift u)
  shift-map k .*→* .prop-setoid._⇒_.func-resp-≈ e = k .func-resp-≈ (λ { zero → refl ; (suc l) → e l })
  shift-map k .preserve-ze i =
    trans (k .func-resp-≈ (λ { zero → refl ; (suc l) → refl }) i) (k .preserve-ze i)
  shift-map k .preserve-+ i =
    trans (k .func-resp-≈ (λ { zero → sym +-lunit ; (suc l) → refl }) i) (k .preserve-+ i)
  shift-map k .preserve-· i =
    trans (k .func-resp-≈ (λ { zero → sym ε-annihilᵣ ; (suc l) → refl }) i)
          (k .preserve-· i)

sum-lin : ∀ {m n} (k : SemiMod._⇒_ (𝔽 m) (𝔽 n)) (v : Vec m) (i : Fin n) →
          k .func v i ≈ Σ {m} (λ j → v j · k .func (M.e j) i)
sum-lin {Nat.zero} k v i = trans (k .func-resp-≈ (λ ()) i) (k .preserve-ze i)
sum-lin {Nat.suc m} k v i =
  trans (k .func-resp-≈ split i)
  (trans (k .preserve-+ i)
         (+-cong (k .preserve-· i)
                 (trans (sum-lin (shift-map k) (λ l → v (suc l)) i)
                        (Σ-cong {m} (λ l → ·-cong refl (k .func-resp-≈ (shift-e l) i))))))
  where
  split : ∀ j → v j ≈ ((v zero · M.e zero j) + shift (λ l → v (suc l)) j)
  split zero    = sym (trans (+-cong (trans ·-comm ·-lunit) refl) (+-runit))
  split (suc l) = sym (trans (+-cong ε-annihilᵣ refl) +-lunit)

𝔽F-faithful : ∀ {m n} {R T : M-cat._⇒_ m n} → SemiMod-cat._≈_ (mat R) (mat T) → M-cat._≈_ R T
𝔽F-faithful {R = R} {T} h i j =
  trans (sym (app-e R j i)) (trans (h .func-eq {M.e j} {M.e j} (λ _ → refl) i) (app-e T j i))

𝔽F-full : ∀ {m n} (k : SemiMod._⇒_ (𝔽 m) (𝔽 n)) → ∃ₛ (M-cat._⇒_ m n) λ R → SemiMod-cat._≈_ (mat R) k
𝔽F-full {m} k = (λ i j → k .func (M.e j) i) ,ₚ pf
  where
  pf : SemiMod-cat._≈_ (mat (λ i j → k .func (M.e j) i)) k
  pf .*≈* .prop-setoid._≃m_.func-eq {u} {v} e i =
    trans (Σ-cong {m} (λ j → trans ·-comm (·-cong (e j) refl))) (sym (sum-lin k v i))
