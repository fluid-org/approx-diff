{-# OPTIONS --prop --postfix-projections --safe #-}

-- Mat(S) embedded in the semimodules, full and faithful: a dimension embeds as the semimodule of
-- weighted vectors over its positions, and a matrix as its action on them. This is the case X = 𝕀
-- of the embedding of Mat(End X) in any biproduct category, presented concretely so that a
-- morphism is read back from its values on the basis. The lifting on each side is the biproduct
-- with the unit object, and the comparison between the two is the canonical comparison of
-- biproducts.
open import Level using (0ℓ)
open import Data.Nat as Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc)
open import prop using (∃ₛ) renaming (_,_ to _,ₚ_)
open import prop-setoid using (Setoid; IsEquivalence)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import categories using (Category; HasTerminal; IsTerminal)
open import cmon-enriched
  using (CMonEnriched; Biproduct; biproduct-iso; biproducts→products)
open import functor using (Functor)
open import finite-product-functor using (preserve-chosen-terminal; preserve-chosen-products)
import lifting
import biproduct-transport
import matrix
import semimodule

module matrix-embedding {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let module S′ = CommutativeSemiring S)
  (⊤-add-top : ∀ {x} → (S′.ι S′.+ x) S′.≈ S′.ι)
  where

open CommutativeSemiring S hiding (_≈_; refl; sym; trans)
open Setoid A

module M = matrix.Mat S
open M
  using (Matrix; Vec; Σ; I; εₘ; _+ₘ_; _≈ₘ_; Σ-cong; Σ-ε; Σ-+; Σ-unit;
         Σ-·-distribₗ; Σ-·-distribᵣ; Σ-interchange;
         ∘-cong; id-left; assoc; comp-bilinear₁; comp-bilinear₂;
         comp-bilinear-ε₁; comp-bilinear-ε₂)
  renaming (_∘_ to _∘ₘ_)
module SemiMod = semimodule S
module SemiModT = SemiMod.Topped ⊤-add-top
open SemiMod using (Semimodule; 𝕀)
open SemiMod._⇒_
open SemiMod._≈m_
open Functor
open Biproduct

private
  module SMC = Category SemiMod.cat
  module MC = Category M.cat
  module SMCM = CMonEnriched SemiMod.cmon-enriched

  +m-cong : ∀ {X Y : Semimodule} {f f' g g' : SemiMod._⇒_ X Y} →
            SMC._≈_ f f' → SMC._≈_ g g' →
            SMC._≈_ (SMCM._+m_ f g) (SMCM._+m_ f' g')
  +m-cong = CommutativeMonoid.+-cong (SMCM.homCM _ _)

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

app-congₘ : ∀ {m n} {R R' : Matrix m n} → R ≈ₘ R' →
            ∀ (v : Vec n) (i : Fin m) → app R v i ≈ app R' v i
app-congₘ {R = R} {R' = R'} h v i = ∘-cong {N₁ = col v} {N₂ = col v} h (λ _ _ → refl) i zero

app-congᵥ : ∀ {m n} (R : Matrix m n) {u w : Vec n} → (∀ j → u j ≈ w j) →
            ∀ (i : Fin m) → app R u i ≈ app R w i
app-congᵥ R {u = u} {w = w} h i =
  ∘-cong {M₁ = R} {M₂ = R} {N₁ = col u} {N₂ = col w} (λ _ _ → refl) (λ j _ → h j) i zero

app-∘ : ∀ {m n k} (R : Matrix m n) (T : Matrix n k) (v : Vec k) (i : Fin m) →
        app (R ∘ₘ T) v i ≈ app R (app T v) i
app-∘ R T v i = assoc R T (col v) i zero

app-+ₘ : ∀ {m n} (R T : Matrix m n) (v : Vec n) (i : Fin m) →
         app (R +ₘ T) v i ≈ (app R v i + app T v i)
app-+ₘ R T v i = comp-bilinear₁ R T (col v) i zero

app-I : ∀ {n} (v : Vec n) (i : Fin n) → app (I {n}) v i ≈ v i
app-I v i = id-left {M = col v} i zero

app-εₘ : ∀ {m n} (v : Vec n) (i : Fin m) → app (εₘ {m} {n}) v i ≈ ε
app-εₘ v i = comp-bilinear-ε₁ (col v) i zero

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

𝔽-⊤ : ℕ → SemiModT.Semimodule-⊤
𝔽-⊤ n .SemiModT.mod = 𝔽 n
𝔽-⊤ n .SemiModT.⊤m _ = ι
𝔽-⊤ n .SemiModT.⊤m-absorb i = trans +-comm ⊤-add-top

mat : ∀ {m n} → Matrix m n → SemiMod._⇒_ (𝔽 n) (𝔽 m)
mat R .*→* .prop-setoid._⇒_.func = app R
mat R .*→* .prop-setoid._⇒_.func-resp-≈ = app-congᵥ R
mat R .preserve-ze = app-ε R
mat R .preserve-+ {u} {v} = app-+ R u v
mat R .preserve-· {s} {u} = app-· R s u

𝔽F : Functor M.cat SemiModT.cat-⊤
𝔽F .fobj = 𝔽-⊤
𝔽F .fmor = mat
𝔽F .fmor-cong {f₂ = R'} h .*≈* .prop-setoid._≃m_.func-eq {u} e i =
  trans (app-congₘ h u i) (app-congᵥ R' e i)
𝔽F .fmor-id .*≈* .prop-setoid._≃m_.func-eq {u} e i = trans (app-I u i) (e i)
𝔽F .fmor-comp f g .*≈* .prop-setoid._≃m_.func-eq {u} e i =
  trans (app-∘ f g u i) (app-congᵥ f (λ j → app-congᵥ g e j) i)

-- The realisation as a homomorphism of the enrichment, which is what the biproduct laws transfer
-- along: composites, sums, the identity and the zero all realise as themselves.
mat-cong : ∀ {m n} {R T : Matrix m n} → R ≈ₘ T → SMC._≈_ (mat R) (mat T)
mat-cong h = 𝔽F .fmor-cong h

mat-comp : ∀ {m n k} (R : Matrix m n) (T : Matrix n k) →
           SMC._≈_ (mat (R ∘ₘ T)) (SemiMod._∘_ (mat R) (mat T))
mat-comp R T = 𝔽F .fmor-comp R T

mat-I : ∀ {n} → SMC._≈_ (mat (I {n})) (SemiMod.id (𝔽 n))
mat-I = 𝔽F .fmor-id

mat-ε : ∀ {m n} → SMC._≈_ (mat (εₘ {m} {n})) (SMCM.εm {𝔽 n} {𝔽 m})
mat-ε .*≈* .prop-setoid._≃m_.func-eq {u} e i = app-εₘ u i

mat-+ : ∀ {m n} (R T : Matrix m n) →
        SMC._≈_ (mat (R +ₘ T)) (SMCM._+m_ (mat R) (mat T))
mat-+ R T .*≈* .prop-setoid._≃m_.func-eq {u} e i =
  trans (app-+ₘ R T u i) (+-cong (app-congᵥ R e i) (app-congᵥ T e i))

------------------------------------------------------------------------------
-- Preservation of the finite products: the biproduct of dimensions realises as a biproduct, with
-- the block matrices as its structure morphisms.

𝔽-biproduct : ∀ m n → Biproduct SemiModT.cmon-enriched-⊤ (𝔽-⊤ m) (𝔽-⊤ n)
𝔽-biproduct m n .prod = 𝔽-⊤ (m +ℕ n)
𝔽-biproduct m n .p₁ = mat (M.p₁ {m} {n})
𝔽-biproduct m n .p₂ = mat (M.p₂ {m} {n})
𝔽-biproduct m n .in₁ = mat (M.in₁ {m} {n})
𝔽-biproduct m n .in₂ = mat (M.in₂ {m} {n})
𝔽-biproduct m n .id-1 =
  SMC.≈-trans (SMC.≈-sym (mat-comp (M.p₁ {m} {n}) (M.in₁ {m} {n})))
              (SMC.≈-trans (mat-cong (M.id-1 m n)) mat-I)
𝔽-biproduct m n .id-2 =
  SMC.≈-trans (SMC.≈-sym (mat-comp (M.p₂ {m} {n}) (M.in₂ {m} {n})))
              (SMC.≈-trans (mat-cong (M.id-2 m n)) mat-I)
𝔽-biproduct m n .zero-1 =
  SMC.≈-trans (SMC.≈-sym (mat-comp (M.p₁ {m} {n}) (M.in₂ {m} {n})))
              (SMC.≈-trans (mat-cong (M.zero-1 m n)) mat-ε)
𝔽-biproduct m n .zero-2 =
  SMC.≈-trans (SMC.≈-sym (mat-comp (M.p₂ {m} {n}) (M.in₁ {m} {n})))
              (SMC.≈-trans (mat-cong (M.zero-2 m n)) mat-ε)
𝔽-biproduct m n .id-+ =
  SMC.≈-trans
    (+m-cong (SMC.≈-sym (mat-comp (M.in₁ {m} {n}) (M.p₁ {m} {n})))
             (SMC.≈-sym (mat-comp (M.in₂ {m} {n}) (M.p₂ {m} {n}))))
    (SMC.≈-trans (SMC.≈-sym (mat-+ (M.in₁ {m} {n} ∘ₘ M.p₁ {m} {n})
                                   (M.in₂ {m} {n} ∘ₘ M.p₂ {m} {n})))
                 (SMC.≈-trans (mat-cong (M.id-+ m n)) mat-I))

𝔽F-preserve-products :
  preserve-chosen-products 𝔽F (biproducts→products M.cmon M.biproduct)
    (biproducts→products SemiModT.cmon-enriched-⊤ SemiModT.biproduct-⊤)
𝔽F-preserve-products {m} {n} =
  biproduct-iso SemiModT.cmon-enriched-⊤ (𝔽-biproduct m n) (SemiModT.biproduct-⊤ (𝔽-⊤ m) (𝔽-⊤ n))

-- The empty dimension realises as the zero module.
𝟘→𝔽0 : SemiMod._⇒_ SemiMod.𝟘 (𝔽 0)
𝟘→𝔽0 .*→* .prop-setoid._⇒_.func _ ()
𝟘→𝔽0 .*→* .prop-setoid._⇒_.func-resp-≈ _ ()
𝟘→𝔽0 .preserve-ze ()
𝟘→𝔽0 .preserve-+ ()
𝟘→𝔽0 .preserve-· ()

𝔽F-preserve-terminal : preserve-chosen-terminal 𝔽F M.terminal SemiModT.terminal-⊤
𝔽F-preserve-terminal .Category.IsIso.inverse = 𝟘→𝔽0
𝔽F-preserve-terminal .Category.IsIso.f∘inverse≈id =
  HasTerminal.to-terminal-unique SemiModT.terminal-⊤ {x = SemiModT.𝟘-⊤} _ (SemiMod.id SemiMod.𝟘)
𝔽F-preserve-terminal .Category.IsIso.inverse∘f≈id .*≈* .prop-setoid._≃m_.func-eq _ ()

------------------------------------------------------------------------------
-- The two liftings: one fresh position on the position side, the scalars on the semimodule side.

module Lm = lifting M.cmon M.biproduct 1
module Ls = lifting SemiModT.cmon-enriched-⊤ SemiModT.biproduct-⊤ SemiModT.𝕀-⊤

-- The unit dimension realises as the scalars.
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

ι1-fwd∘bwd : SemiMod._≈m_ {𝕀} {𝕀} (SemiMod._∘_ {𝕀} {𝔽 1} {𝕀} ι1-fwd ι1-bwd) (SemiMod.id 𝕀)
ι1-fwd∘bwd .*≈* .prop-setoid._≃m_.func-eq e = e

ι1-bwd∘fwd : SemiMod._≈m_ {𝔽 1} {𝔽 1}
               (SemiMod._∘_ {𝔽 1} {𝕀} {𝔽 1} ι1-bwd ι1-fwd) (SemiMod.id (𝔽 1))
ι1-bwd∘fwd .*≈* .prop-setoid._≃m_.func-eq e = λ { zero → e zero }

module BT = biproduct-transport SemiModT.cmon-enriched-⊤

-- The realisation of a lifted dimension is a biproduct of the scalars and the realised payload:
-- the block witness with its first leg conjugated by the scalar comparison.
L-biproduct : ∀ n → Biproduct SemiModT.cmon-enriched-⊤ SemiModT.𝕀-⊤ (𝔽-⊤ n)
L-biproduct n = BT.transport₁ (𝔽-biproduct 1 n) ι1-fwd ι1-bwd ι1-fwd∘bwd ι1-bwd∘fwd

𝔽-L-iso : ∀ n → Category.Iso SemiModT.cat-⊤
                  (𝔽-⊤ (Lm.L n)) (Ls.L (𝔽-⊤ n))
𝔽-L-iso n =
  Category.IsIso→Iso SemiModT.cat-⊤
    (biproduct-iso SemiModT.cmon-enriched-⊤ (L-biproduct n) (SemiModT.biproduct-⊤ SemiModT.𝕀-⊤ (𝔽-⊤ n)))

-- The lifted action realises as the copairing over the block witness, which is the form the
-- comparison's naturality is stated against.
mat-Lmap : ∀ {P Q} (f : Category._⇒_ M.cat P Q) →
           SMC._≈_ (mat (Lm.Lmap f))
                   (copair (𝔽-biproduct 1 P) {x = 𝔽-⊤ (Lm.L Q)}
                           (𝔽-biproduct 1 Q .in₁)
                           (SemiMod._∘_ (𝔽-biproduct 1 Q .in₂) (mat f)))
mat-Lmap {P} {Q} f =
  SMC.≈-trans (mat-+ (M.in₁ {1} {Q} ∘ₘ M.p₁ {1} {P}) ((M.in₂ {1} {Q} ∘ₘ f) ∘ₘ M.p₂ {1} {P}))
    (+m-cong
      (mat-comp (M.in₁ {1} {Q}) (M.p₁ {1} {P}))
      (SMC.≈-trans (mat-comp (M.in₂ {1} {Q} ∘ₘ f) (M.p₂ {1} {P}))
                   (SMC.∘-cong (mat-comp (M.in₂ {1} {Q}) f) (SMC.≈-refl {f = mat (M.p₂ {1} {P})}))))

𝔽-L-natural : ∀ {P Q} (f : Category._⇒_ M.cat P Q) →
  SMC._≈_ (SemiMod._∘_ (𝔽-L-iso Q .Category.Iso.fwd) (mat (Lm.Lmap f)))
          (SemiMod._∘_ (Ls.Lmap {𝔽-⊤ P} {𝔽-⊤ Q} (mat f))
                       (𝔽-L-iso P .Category.Iso.fwd))
𝔽-L-natural {P} {Q} f =
  SMC.≈-trans
    (SMC.∘-cong (SMC.≈-refl {f = 𝔽-L-iso Q .Category.Iso.fwd}) (mat-Lmap f))
    (BT.compare-natural
      (𝔽-biproduct 1 P) (𝔽-biproduct 1 Q)
      (SemiModT.biproduct-⊤ SemiModT.𝕀-⊤ (𝔽-⊤ P)) (SemiModT.biproduct-⊤ SemiModT.𝕀-⊤ (𝔽-⊤ Q))
      ι1-fwd ι1-bwd ι1-fwd∘bwd ι1-bwd∘fwd (mat f))

------------------------------------------------------------------------------
-- The realisation is full and faithful: a linear map between free semimodules is the matrix of
-- its values on the basis, so a fibre map of the model is a weighted relation and nothing else.

-- The image of a basis vector reads off an entry.
app-e : ∀ {m n} (R : Matrix m n) (j : Fin n) (i : Fin m) → app R (M.e j) i ≈ R i j
app-e {m} {n} R j i =
  trans (Σ-cong {n} (λ l → ·-comm)) (Σ-unit j (λ l → R i l))

private
  -- Padding a vector with a zero at the head, and the map it induces on linear maps: the
  -- restriction of a map on suc m positions to the positions under the head.
  shift : ∀ {m} → Vec m → Vec (Nat.suc m)
  shift u zero    = ε
  shift u (suc l) = u l

  shift-e : ∀ {m} (l : Fin m) (j : Fin (Nat.suc m)) → shift (M.e l) j ≈ M.e (suc l) j
  shift-e l zero     = refl
  shift-e l (suc j') = refl

  shift-map : ∀ {m n} → SemiMod._⇒_ (𝔽 (Nat.suc m)) (𝔽 n) → SemiMod._⇒_ (𝔽 m) (𝔽 n)
  shift-map k .*→* .prop-setoid._⇒_.func u = k .func (shift u)
  shift-map k .*→* .prop-setoid._⇒_.func-resp-≈ e =
    k .func-resp-≈ (λ { zero → refl ; (suc l) → e l })
  shift-map k .preserve-ze i =
    trans (k .func-resp-≈ (λ { zero → refl ; (suc l) → refl }) i) (k .preserve-ze i)
  shift-map k .preserve-+ i =
    trans (k .func-resp-≈ (λ { zero → sym +-lunit ; (suc l) → refl }) i) (k .preserve-+ i)
  shift-map k .preserve-· i =
    trans (k .func-resp-≈ (λ { zero → sym ε-annihilᵣ ; (suc l) → refl }) i)
          (k .preserve-· i)

-- A linear map is the weighted sum of its values on the basis.
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
  split zero    = sym (trans (+-cong (trans ·-comm ·-lunit) refl) (trans +-comm +-lunit))
  split (suc l) = sym (trans (+-cong ε-annihilᵣ refl) +-lunit)

𝔽F-faithful : ∀ {m n} {R T : Category._⇒_ M.cat m n} → SMC._≈_ (mat R) (mat T) → MC._≈_ R T
𝔽F-faithful {R = R} {T} h i j =
  trans (sym (app-e R j i)) (trans (h .func-eq {M.e j} {M.e j} (λ _ → refl) i) (app-e T j i))

𝔽F-full : ∀ {m n} (k : SemiMod._⇒_ (𝔽 m) (𝔽 n)) →
          ∃ₛ (Category._⇒_ M.cat m n) λ R → SMC._≈_ (mat R) k
𝔽F-full {m} k = (λ i j → k .func (M.e j) i) ,ₚ pf
  where
  pf : SMC._≈_ (mat (λ i j → k .func (M.e j) i)) k
  pf .*≈* .prop-setoid._≃m_.func-eq {u} {v} e i =
    trans (Σ-cong {m} (λ j → trans ·-comm (·-cong (e j) refl))) (sym (sum-lin k v i))
